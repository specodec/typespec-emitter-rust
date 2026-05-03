import {
  EmitContext, emitFile, listServices, navigateTypesInNamespace,
  Model, Namespace, Interface, Program, Type, Scalar, Diagnostic,
} from "@typespec/compiler";
import {
  checkReservedKeyword,
  formatReservedError,
  isSpecodecModel,
} from "@specodec/typespec-emitter-core";

export type EmitterOptions = { "emitter-output-dir": string; "ignore-reserved-keywords"?: boolean };

interface FieldInfo { name: string; type: Type; optional: boolean; }
interface ServiceInfo { namespace: Namespace; iface?: Interface; serviceName: string; models: Model[]; }

function extractFields(model: Model): FieldInfo[] {
  const fields: FieldInfo[] = [];
  for (const [name, prop] of model.properties) fields.push({ name, type: prop.type, optional: prop.optional ?? false });
  return fields;
}

function scalarName(t: Type): string { return t.kind === "Scalar" ? (t as Scalar).name : ""; }
function isArray(t: Type): boolean {
  if (t.kind !== "Model" || !(t as Model).indexer) return false;
  const keyName = ((t as Model).indexer!.key as any).name;
  return keyName === "integer";
}
function isRecord(t: Type): boolean {
  if (t.kind !== "Model" || !(t as Model).indexer) return false;
  const keyName = ((t as Model).indexer!.key as any).name;
  return keyName === "string";
}
function isModel(t: Type): boolean { return t.kind === "Model" && !!(t as Model).name && !isArray(t) && !isRecord(t); }
function arrayElem(t: Type): Type { return (t as Model).indexer!.value; }
function recordElem(t: Type): Type { return (t as Model).indexer!.value; }

function typeToRust(t: Type): string {
  if (isArray(t)) return `Vec<${typeToRust(arrayElem(t))}>`;
  if (isRecord(t)) return `std::collections::HashMap<String, ${typeToRust(recordElem(t))}>`;
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
  if (isRecord(t)) return "std::collections::HashMap::new()";
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
  if (isRecord(fieldType)) {
    const elem = recordElem(fieldType);
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

// Single format-agnostic write expression using SpecWriter
function writeExpr(t: Type, expr: string): string {
  if (isArray(t)) {
    const elem = arrayElem(t);
    const lenExpr = expr.startsWith("&") ? expr.substring(1) : expr;
    return `w.begin_array(${lenExpr}.len()); for _e in ${expr} { w.next_element(); ${writeExpr(elem, "_e")} }; w.end_array()`;
  }
  if (isRecord(t)) {
    const elem = recordElem(t);
    const lenExpr = expr.startsWith("&") ? expr.substring(1) : expr;
    return `w.begin_object(${lenExpr}.len()); for (_k, _v) in ${expr} { w.write_field(_k); ${writeExpr(elem, "_v")} }; w.end_object()`;
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
    return `${toSnake((t as Model).name)}_write(${expr}, w)`;
  }
  return `w.write_string(${expr})`;
}

function readExpr(t: Type, optional?: boolean, needsBox?: boolean): string {
  const wrapBox = (expr: string) => needsBox ? `Box::new(${expr})` : expr;
  
  if (isArray(t)) {
    const elem = arrayElem(t);
    const rt = typeToRust(elem);
    const arrExpr = `{ let mut _arr: Vec<${rt}> = Vec::new(); r.begin_array()?; while r.has_next_element()? { _arr.push(${readExpr(elem, false, false)}); } r.end_array()?; _arr }`;
    if (optional) return `Some(${arrExpr})`;
    return arrExpr;
  }
  if (isRecord(t)) {
    const elem = recordElem(t);
    const rt = typeToRust(elem);
    const mapExpr = `{ let mut _map: std::collections::HashMap<String, ${rt}> = std::collections::HashMap::new(); r.begin_object()?; while r.has_next_field()? { let _k = r.read_field_name()?; _map.insert(_k, ${readExpr(elem, false, false)}); } r.end_object()?; _map }`;
    if (optional) return `Some(${mapExpr})`;
    return mapExpr;
  }
  const s = scalarName(t);
  let expr: string;
  switch (s) {
    case "string": expr = "r.read_string()?"; break;
    case "boolean": expr = "r.read_bool()?"; break;
    case "int8": expr = "r.read_int32()? as i8"; break;
    case "int16": expr = "r.read_int32()? as i16"; break;
    case "int32": case "integer": expr = "r.read_int32()?"; break;
    case "int64": expr = "r.read_int64()?"; break;
    case "uint8": expr = "r.read_uint32()? as u8"; break;
    case "uint16": expr = "r.read_uint32()? as u16"; break;
    case "uint32": expr = "r.read_uint32()?"; break;
    case "uint64": expr = "r.read_uint64()?"; break;
    case "float32": expr = "r.read_float32()?"; break;
    case "float64": case "float": case "decimal": expr = "r.read_float64()?"; break;
    case "bytes": expr = "r.read_bytes()?"; break;
    default:
      if (t.kind === "Model" && (t as Model).name) {
        const decodeCall = `${toSnake((t as Model).name)}_decode(r)?`;
        const boxedCall = wrapBox(decodeCall);
        if (optional) return `if r.is_null()? { r.read_null()?; None } else { Some(${boxedCall}) }`;
        return boxedCall;
      }
      expr = "r.read_string()?"; break;
  }
  if (optional) return `Some(${expr})`;
  return expr;
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
    navigateTypesInNamespace(ns, { model: (m: Model) => { if (m.name && !seen.has(m.name) && isSpecodecModel(program, m)) { models.push(m); seen.add(m.name); } } });
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
    lines.push("use specodec::{SpecWriter, SpecReader, SpecCodec, SCodecError};");
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

      // ${snake}_write — format-agnostic write using SpecWriter
      lines.push(`pub fn ${snake}_write(obj: &${m.name}, w: &mut dyn SpecWriter) {`);
      const req = countRequiredFields(fields);
      const optFields = fields.filter(f => f.optional);
      lines.push(`    let mut _n: usize = ${req};`);
      for (const f of optFields) {
        lines.push(`    if obj.${f.name}.is_some() { _n += 1; }`);
      }
      lines.push(`    w.begin_object(_n);`);
      for (const f of fields) {
        if (f.optional) {
          lines.push(`    if let Some(ref _v) = obj.${f.name} { w.write_field("${f.name}"); ${writeExpr(f.type, "_v")}; }`);
        } else {
          const expr = fieldRef(f);
          lines.push(`    w.write_field("${f.name}"); ${writeExpr(f.type, expr)};`);
        }
      }
      lines.push(`    w.end_object();`);
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
        if (f.optional) {
          lines.push(`            "${f.name}" => { _${f.name} = ${readExpr(f.type, true, box)}; }`);
        } else {
          lines.push(`            "${f.name}" => { _${f.name} = ${readExpr(f.type, false, box)}; }`);
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

      lines.push(`#[allow(non_upper_case_globals)]`);
      lines.push(`pub static ${m.name}Codec: SpecCodec<${m.name}> = SpecCodec {`);
      lines.push(`    encode: ${snake}_write,`);
      lines.push(`    decode: ${snake}_decode,`);
      lines.push(`};`);
      lines.push("");
    }

    const snakeSvc = toSnake(svc.serviceName);
    await emitFile(program, { path: `${outputDir}/${snakeSvc}_types.rs`, content: lines.join("\n") });
  }
}
