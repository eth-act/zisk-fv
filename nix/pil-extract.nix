{ rustPlatform, lib, protobuf }:

rustPlatform.buildRustPackage {
  pname = "pil-extract";
  version = "0.1.0";

  src = lib.cleanSourceWith {
    src = ../tools/pil-extract;
    filter = path: type:
      let baseName = baseNameOf (toString path);
      in baseName != "target" && baseName != "Cargo.lock.bak";
  };

  cargoLock = {
    lockFile = ../tools/pil-extract/Cargo.lock;
  };

  # prost-build (build.rs) needs protoc on PATH.
  nativeBuildInputs = [ protobuf ];

  meta = with lib; {
    description = "Extract Lean4 constraint definitions from ZisK pilout";
    license = with licenses; [ asl20 mit ];
    mainProgram = "pil-extract";
  };
}
