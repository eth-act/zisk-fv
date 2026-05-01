{
  description = "zisk-fv: Lean 4 formal verification of ZisK against Sail RISC-V";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-25.05";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
      in {
        devShells.default = pkgs.mkShell {
          buildInputs = with pkgs; [
            elan         # Lean toolchain manager
            cargo
            rustc
            python3
            jq
            git
          ];
        };
      });
}
