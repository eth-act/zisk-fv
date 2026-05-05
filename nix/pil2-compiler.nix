{ buildNpmPackage, pil2-compiler-src, lib }:

# pil2-compiler is the JavaScript PIL2 compiler. We package its
# node_modules tree so the Node-driven PIL compile step inside
# zisk-pilout can `require()` deterministically.
#
# We don't run any "build" step (no jison generation etc.) — pil2-compiler
# ships with src/pil_parser.js already generated. `dontNpmBuild = true`
# skips that.
buildNpmPackage {
  pname = "pil2-compiler";
  version = "0.9.0";  # tag we pin

  src = pil2-compiler-src;

  # First build will fail with a hash mismatch error; nix will print
  # the correct value to paste back in here.
  npmDepsHash = "sha256-Ugdu3E/USOPR7gBtj6MClx80PfShSR6Yqsj96BsFFHk=";

  dontNpmBuild = true;
  dontFixup = true;

  installPhase = ''
    runHook preInstall
    mkdir -p $out
    cp -r . $out/
    runHook postInstall
  '';

  meta = with lib; {
    description = "PIL2 compiler with vendored node_modules";
    license = with licenses; [ asl20 mit ];
  };
}
