fn main() -> Result<(), Box<dyn std::error::Error>> {
    prost_build::compile_protos(&["proto/pilout.proto"], &["proto/"])?;
    println!("cargo:rerun-if-changed=proto/pilout.proto");
    Ok(())
}
