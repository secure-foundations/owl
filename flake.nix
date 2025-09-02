{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs-ghc.url = "github:NixOS/nixpkgs/79b3d4bcae8c7007c9fd51c279a8a67acfa73a2a";
    nixpkgs-cabal.url = "github:NixOS/nixpkgs/7cf5ccf1cdb2ba5f08f0ac29fc3d04b0b59a07e4";
  };
  outputs = {
    self,
    nixpkgs,
    flake-utils,
    nixpkgs-ghc,
    nixpkgs-cabal,
    ...
  } @ inputs:
    inputs.flake-utils.lib.eachDefaultSystem (system:
      let
        name = "owl-flake";
        src = ./.;
        pkgs = nixpkgs.legacyPackages.${system};
        pkgs-ghc = nixpkgs-ghc.legacyPackages.${system};
        pkgs-cabal = nixpkgs-cabal.legacyPackages.${system};
        
        z3-binary = pkgs.stdenv.mkDerivation {
          pname = "z3-bin";
          version = "4.12.1";
          
          src = pkgs.fetchzip {
            url = "https://github.com/Z3Prover/z3/releases/download/z3-4.12.1/z3-4.12.1-x64-glibc-2.35.zip";
            sha256 = "0hlfz8d7n1q78c015l8ygf91674wx5xjgg1b52sbh00armdbfxw4";
          };
          
          # need autoPatchelfHook to fix the binary's dynamic linking
          nativeBuildInputs = [ pkgs.autoPatchelfHook ];
          buildInputs = [ pkgs.stdenv.cc.cc.lib ];
          
          installPhase = ''
            mkdir -p $out
            cp -r * $out/
            chmod +x $out/bin/z3
            chmod +x $out/bin/*.so 2>/dev/null || true
          '';
        };
      in {
        inherit name src;
        
        devShells.default = pkgs.mkShell {
          buildInputs = with pkgs; [
            z3-binary
            
            # haskell toolchain
            # ghc
            # cabal-installs
            
            # c compiler and libraries (for z3)
            stdenv.cc.cc
            glib
            zlib
          ] ++ [
            pkgs-ghc.ghc
            pkgs-cabal.cabal-install
          ];
          
          shellHook = ''
            echo "owl flake indeed"
            echo "z3 available at: $(which z3)"
            echo "ghc version: $(ghc --version)"
            echo "cabal version: $(cabal --version | head -n1)"
          '';
        };
      }
    );
}
