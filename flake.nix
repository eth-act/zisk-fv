{
  description = "zisk-fv: Lean 4 formal verification of ZisK against Sail RISC-V";

  inputs = {
    # nixos-unstable for sail 0.20+ (25.05 ships sail 0.19, which our
    # pinned sail-riscv source rejects). flake.lock pins the exact rev.
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";

    # Pinned upstream sources. Same commits/tags as the deleted
    # docker/versions.txt; flake.lock is now the audit surface.
    sail-src = {
      url = "github:rems-project/sail/277470b2ab472af8064e1295be5573845239c96b";
      flake = false;
    };
    sail-riscv-src = {
      url = "github:riscv/sail-riscv/04e595954b2af7fa9e18f2519e4ae4bba72b2701";
      flake = false;
    };
    zisk-src = {
      url = "github:0xPolygonHermez/zisk/v0.17.0";
      flake = false;
    };
    pil2-compiler-src = {
      url = "github:0xPolygonHermez/pil2-compiler/v0.9.0";
      flake = false;
    };
    pil2-proofman-src = {
      url = "github:0xPolygonHermez/pil2-proofman/v0.17.0";
      flake = false;
    };
  };

  outputs = { self, nixpkgs, flake-utils, sail-src, sail-riscv-src,
              zisk-src, pil2-compiler-src, pil2-proofman-src }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
      in {
        packages.pil-extract = pkgs.callPackage ./nix/pil-extract.nix { };

        packages.sail-lean-tree = pkgs.callPackage ./nix/sail-lean-tree.nix {
          inherit sail-riscv-src;
        };

        packages.pil2-compiler = pkgs.callPackage ./nix/pil2-compiler.nix {
          inherit pil2-compiler-src;
        };

        packages.zisk-pilout = pkgs.callPackage ./nix/zisk-pilout.nix {
          inherit zisk-src pil2-proofman-src;
          pil2-compiler = self.packages.${system}.pil2-compiler;
        };

        packages.extracted-lean = pkgs.callPackage ./nix/extracted-lean.nix {
          pil-extract = self.packages.${system}.pil-extract;
          zisk-pilout = self.packages.${system}.zisk-pilout;
        };

        apps.populate = {
          type = "app";
          program = "${pkgs.callPackage ./nix/populate.nix {
            sail-lean-tree = self.packages.${system}.sail-lean-tree;
            zisk-pilout = self.packages.${system}.zisk-pilout;
            extracted-lean = self.packages.${system}.extracted-lean;
          }}/bin/populate";
        };

        apps.test = {
          type = "app";
          program = "${pkgs.callPackage ./nix/test.nix { }}/bin/test";
        };

        devShells.default = pkgs.mkShell {
          buildInputs = with pkgs; [
            elan         # Lean toolchain manager
            cargo
            rustc
            protobuf     # protoc, used by tools/pil-extract's build.rs
            python3
            jq
            git
          ];
        };
      });
}
