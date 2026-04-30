import {
  EmitContext, emitFile, listServices, navigateTypesInNamespace,
  Model, Namespace, Interface, Program, Type, Scalar, Diagnostic,
} from "@typespec/compiler";
import {
  checkReservedKeyword,
  formatReservedError,
} from "@specodec/typespec-specodec-core";

export type EmitterOptions = { "emitter-output-dir": string; "ignore-reserved-keywords"?: boolean };

interface FieldInfo { name: string; type: Type; optional: boolean; }
interface ServiceInfo { namespace: Namespace; iface?: Interface; serviceName: string; models: Model[]; }

function extractFields(model: Model): FieldInfo[] {
  const fields: FieldInfo[] = [];
  for (const [name, prop] of model.properties) fields.push({ name, type: prop.type, optional: prop.optional ?? false });
  return fields;
}

function scalarName(t: Type): string { return t.kind === "Scalar" ? (t as Scalar).name : ""; }
function isArray(t: Type): boolean { return t.kind === "Model" && !!(t as Model).indexer; }
function isModel(t: Type): boolean { return t.kind === "Model" && !!(t as Model).name && !isArray(t); }
function arrayElem(t: Type): Type { return (t as Model).indexer!.value; }

function typeToRust(t: Type): string {
  if (isArray(t)) return `Vec<${typeToRust(arrayElem(t))}>`;
  const s = scalarName(t);
  switch (s) {
    case "string": return "String";
    case "boolean": return "bool";
    case "int8": return "i8";
    case "int16": return "i16";
    case "int32": case "integer": return "i32";
    case "int64": return "i64";
    case "uint8": return "u8";
    case "uint16": return "u16";
    case "uint32": return "u32";
    case "uint64": return "u64";
    case "float32": return "f32";
    case "float64": case "float": case "decimal": return "f64";
    case "bytes": return "Vec<u8>";
  }
  if (t.kind === "Model" && (t as Model).name) return (t as Model).name;
  return "String";
}

function defaultFor(t: Type): string {
  const s = scalarName(t);
  if (s === "string") return "String::new()";
  if (s === "boolean") return "false";
  if (s === "float32" || s === "float64" || s === "float" || s === "decimal") return "0.0";
  if (s === "bytes") return "Vec::new()";
  if (isArray(t)) return "Vec::new()";
  if (["int8","int16","int32","int64","uint8","uint16","uint32","uint64","integer"].includes(s)) return "0";
  if (isModel(t)) return `${(t as Model).name} { ..Default::default() }`;
  return "String::new()";
}

function needsBox(fieldType: Type, structName: string): boolean {
  if (fieldType.kind === "Model" && (fieldType as Model).name === structName) return true;
  if (isArray(fieldType)) {
    const elem = arrayElem(fieldType);
    if (elem.kind === "Model" && (elem as Model).name === structName) return true;
  }
  return false;
}

function typeToRustField(t: Type, optional: boolean, structName: string): string {
  const rt = typeToRust(t);
  const box = needsBox(t, structName);
  if (optional) {
    return box ? `Option<Box<${rt}>>` : `Option<${rt}>`;
  }
  return box ? `Box<${rt}>` : rt;
}

function fieldRef(f: FieldInfo): string {
  return `&obj.${f.name}`;
}

function writeJsonExpr(t: Type, expr: string): string {
  if (isArray(t)) {
    const elem = arrayElem(t);
    return `w.begin_array(); for _e in ${expr} { w.next_element(); ${writeJsonExpr(elem, "_e")} }; w.end_array()`;
  }
  const s = scalarName(t);
  switch (s) {
    case "string": return `w.write_string(${expr})`;
    case "boolean": return `w.write_bool(*${expr})`;
    case "int8": return `w.write_int32(*${expr} as i32)`;
    case "int16": return `w.write_int32(*${expr} as i32)`;
    case "int32": case "integer": return `w.write_int32(*${expr})`;
    case "int64": return `w.write_int64(*${expr})`;
    case "uint8": return `w.write_uint32(*${expr} as u32)`;
    case "uint16": return `w.write_uint32(*${expr} as u32)`;
    case "uint32": return `w.write_uint32(*${expr})`;
    case "uint64": return `w.write_uint64(*${expr})`;
    case "float32": return `w.write_float32(*${expr})`;
    case "float64": case "float": case "decimal": return `w.write_float64(*${expr})`;
    case "bytes": return `w.write_bytes(${expr})`;
  }
  if (t.kind === "Model" && (t as Model).name) {
    const fn_ = toSnake((t as Model).name) + "_encode_json_inner";
    return `${fn_}(${expr}, w)`;
  }
  return `w.write_string(${expr})`;
}

function writeMsgPackExpr(t: Type, expr: string): string {
  if (isArray(t)) {
    const elem = arrayElem(t);
    const lenExpr = expr.startsWith("&") ? expr.substring(1) : expr;
    return `w.begin_array(${lenExpr}.len()); for _e in ${expr} { w.next_element(); ${writeMsgPackExpr(elem, "_e")} }; w.end_array()`;
  }
  const s = scalarName(t);
  switch (s) {
    case "string": return `w.write_string(${expr})`;
    case "boolean": return `w.write_bool(*${expr})`;
    case "int8": return `w.write_int32(*${expr} as i32)`;
    case "int16": return `w.write_int32(*${expr} as i32)`;
    case "int32": case "integer": return `w.write_int32(*${expr})`;
    case "int64": return `w.write_int64(*${expr})`;
    case "uint8": return `w.write_uint32(*${expr} as u32)`;
    case "uint16": return `w.write_uint32(*${expr} as u32)`;
    case "uint32": return `w.write_uint32(*${expr})`;
    case "uint64": return `w.write_uint64(*${expr})`;
    case "float32": return `w.write_float32(*${expr})`;
    case "float64": case "float": case "decimal": return `w.write_float64(*${expr})`;
    case "bytes": return `w.write_bytes(${expr})`;
  }
  if (t.kind === "Model" && (t as Model).name) {
    const fn_ = toSnake((t as Model).name) + "_encode_msgpack_inner";
    return `${fn_}(${expr}, w)`;
  }
  return `w.write_string(${expr})`;
}

function readExpr(t: Type): string {
  if (isArray(t)) {
    const elem = arrayElem(t);
    const rt = typeToRust(elem);
    return `{ let mut _arr: Vec<${rt}> = Vec::new(); r.begin_array()?; while r.has_next_element()? { _arr.push(${readExpr(elem)}); } r.end_array()?; _arr }`;
  }
  const s = scalarName(t);
  switch (s) {
    case "string": return "r.read_string()?";
    case "boolean": return "r.read_bool()?";
    case "int8": return "r.read_int32()? as i8";
    case "int16": return "r.read_int32()? as i16";
    case "int32": case "integer": return "r.read_int32()?";
    case "int64": return "r.read_int64()?";
    case "uint8": return "r.read_uint32()? as u8";
    case "uint16": return "r.read_uint32()? as u16";
    case "uint32": return "r.read_uint32()?";
    case "uint64": return "r.read_uint64()?";
    case "float32": return "r.read_float32()?";
    case "float64": case "float": case "decimal": return "r.read_float64()?";
    case "bytes": return "r.read_bytes()?";
  }
  if (t.kind === "Model" && (t as Model).name) return `${toSnake((t as Model).name)}_decode(r)?`;
  return "r.read_string()?";
}

function toSnake(name: string): string {
  return name.replace(/([A-Z])/g, (m, c, i) => (i ? "_" : "") + c.toLowerCase());
}

function toScreaming(name: string): string {
  return toSnake(name).toUpperCase();
}

function countRequiredFields(fields: FieldInfo[]): number {
  return fields.filter(f => !f.optional).length;
}

function collectServices(program: Program): ServiceInfo[] {
  const services = listServices(program);
  const result: ServiceInfo[] = [];
  function collectFromNs(ns: Namespace, iface?: Interface) {
    const models: Model[] = []; const seen = new Set<string>();
    navigateTypesInNamespace(ns, { model: (m: Model) => { if (m.name && !seen.has(m.name)) { models.push(m); seen.add(m.name); } } });
    if (models.length > 0) {
      result.push({ 
        namespace: ns, 
        iface: iface || { name: ns.name || "TestService", namespace: ns } as Interface, 
        serviceName: iface?.name || ns.name || "TestService", 
        models 
      });
    }
  }
  for (const svc of services) collectFromNs(svc.type);
  if (result.length === 0) {
    const g = program.getGlobalNamespaceType();
    for (const [, ns] of g.namespaces) collectFromNs(ns);
    collectFromNs(g);
  }
  return result;
}

export async function $onEmit(context: EmitContext<EmitterOptions>) {
  const program = context.program;
  const outputDir = context.emitterOutputDir;
  const ignoreReservedKeywords = context.options["ignore-reserved-keywords"] ?? false;
  const services = collectServices(program);

  const reservedFieldErrors: Diagnostic[] = [];
  for (const svc of services) {
    for (const m of svc.models) {
      if (!m.name) continue;
      for (const [fieldName, prop] of m.properties) {
        const reservedIn = checkReservedKeyword(fieldName);
        if (reservedIn.length > 0) {
          const message = formatReservedError(fieldName, m.name, reservedIn);
          const diag: Diagnostic = {
            severity: "error",
            code: "reserved-keyword",
            message,
            target: prop,
          };
          reservedFieldErrors.push(diag);
        }
      }
    }
  }

  if (reservedFieldErrors.length > 0 && !ignoreReservedKeywords) {
    program.reportDiagnostics(reservedFieldErrors);
    return;
  }

  if (reservedFieldErrors.length > 0 && ignoreReservedKeywords) {
    for (const diag of reservedFieldErrors) {
      console.warn(`Warning: ${diag.message}`);
    }
  }

  for (const svc of services) {
    const lines: string[] = [];
    lines.push("// Generated by @specodec/typespec-specodec-rust. DO NOT EDIT.");
    lines.push("use specodec::{JsonWriter, MsgPackWriter, SpecReader, SpecCodec, SCodecError};");
    lines.push("");

    for (const m of svc.models) {
      if (!m.name) continue;
      const fields = extractFields(m);
      const snake = toSnake(m.name);
      const screaming = toScreaming(m.name);

      lines.push(`#[derive(Debug, Clone, Default)]`);
      lines.push(`pub struct ${m.name} {`);
      for (const f of fields) {
        lines.push(`    pub ${f.name}: ${typeToRustField(f.type, f.optional, m.name)},`);
      }
      lines.push(`}`);
      lines.push("");

      // _encode_json_inner — takes a &mut JsonWriter
      lines.push(`pub fn ${snake}_encode_json_inner(obj: &${m.name}, w: &mut JsonWriter) {`);
      lines.push(`    w.begin_object();`);
      for (const f of fields) {
        if (f.optional) {
          lines.push(`    if let Some(ref _v) = obj.${f.name} { w.write_field("${f.name}"); ${writeJsonExpr(f.type, "_v")}; }`);
        } else {
          const expr = fieldRef(f);
          lines.push(`    w.write_field("${f.name}"); ${writeJsonExpr(f.type, expr)};`);
        }
      }
      lines.push(`    w.end_object();`);
      lines.push(`}`);
      lines.push("");

      // encode_json — public API
      lines.push(`pub fn ${snake}_encode_json(obj: &${m.name}) -> Vec<u8> {`);
      lines.push(`    let mut w = JsonWriter::new();`);
      lines.push(`    ${snake}_encode_json_inner(obj, &mut w);`);
      lines.push(`    w.into_bytes()`);
      lines.push(`}`);
      lines.push("");

      // _encode_msgpack_inner — takes a &mut MsgPackWriter
      lines.push(`pub fn ${snake}_encode_msgpack_inner(obj: &${m.name}, w: &mut MsgPackWriter) {`);
      const req = countRequiredFields(fields);
      const optFields = fields.filter(f => f.optional);
      lines.push(`    let mut _n: usize = ${req};`);
      for (const f of optFields) {
        lines.push(`    if obj.${f.name}.is_some() { _n += 1; }`);
      }
      lines.push(`    w.begin_object(_n);`);
      for (const f of fields) {
        if (f.optional) {
          lines.push(`    if let Some(ref _v) = obj.${f.name} { w.write_field("${f.name}"); ${writeMsgPackExpr(f.type, "_v")}; }`);
        } else {
          const expr = fieldRef(f);
          lines.push(`    w.write_field("${f.name}"); ${writeMsgPackExpr(f.type, expr)};`);
        }
      }
      lines.push(`    w.end_object();`);
      lines.push(`}`);
      lines.push("");

      // encode_msgpack — public API
      lines.push(`pub fn ${snake}_encode_msgpack(obj: &${m.name}) -> Vec<u8> {`);
      lines.push(`    let mut w = MsgPackWriter::new();`);
      lines.push(`    ${snake}_encode_msgpack_inner(obj, &mut w);`);
      lines.push(`    w.into_bytes()`);
      lines.push(`}`);
      lines.push("");

      // decode
      lines.push(`pub fn ${snake}_decode(r: &mut dyn SpecReader) -> Result<${m.name}, SCodecError> {`);
      for (const f of fields) {
        const rt = typeToRust(f.type);
        const box = needsBox(f.type, m.name);
        if (f.optional) {
          const varType = box ? `Option<Box<${rt}>>` : `Option<${rt}>`;
          lines.push(`    let mut _${f.name}: ${varType} = None;`);
        } else {
          const varType = box ? `Box<${rt}>` : rt;
          const defVal = box ? `Box::new(${defaultFor(f.type)})` : defaultFor(f.type);
          lines.push(`    let mut _${f.name}: ${varType} = ${defVal};`);
        }
      }
      lines.push(`    r.begin_object()?;`);
      lines.push(`    while r.has_next_field()? {`);
      lines.push(`        match r.read_field_name()?.as_str() {`);
      for (const f of fields) {
        const box = needsBox(f.type, m.name);
        const wrapBox = (expr: string) => box ? `Box::new(${expr})` : expr;
        if (f.optional) {
          lines.push(`            "${f.name}" => { _${f.name} = Some(${wrapBox(readExpr(f.type))}); }`);
        } else {
          lines.push(`            "${f.name}" => { _${f.name} = ${wrapBox(readExpr(f.type))}; }`);
        }
      }
      lines.push(`            _ => { r.skip()?; }`);
      lines.push(`        }`);
      lines.push(`    }`);
      lines.push(`    r.end_object()?;`);
      const constructFields = fields.map(f => `${f.name}: _${f.name}`).join(", ");
      lines.push(`    Ok(${m.name} { ${constructFields} })`);
      lines.push(`}`);
      lines.push("");

      lines.push(`pub static ${screaming}_CODEC: SpecCodec<${m.name}> = SpecCodec {`);
      lines.push(`    encode_json: ${snake}_encode_json,`);
      lines.push(`    encode_msgpack: ${snake}_encode_msgpack,`);
      lines.push(`    decode: ${snake}_decode,`);
      lines.push(`};`);
      lines.push("");
    }

    const snakeSvc = toSnake(svc.serviceName);
    await emitFile(program, { path: `${outputDir}/${snakeSvc}_types.rs`, content: lines.join("\n") });
  }
}
