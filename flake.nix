{
  description = "A chapter-by-chapter, tacticless Lean formalization of Principles of Program Analysis";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

  outputs = { self, nixpkgs }:
    let
      system = "x86_64-linux";
      pkgs = import nixpkgs { inherit system; };
    in {
      devShells.${system}.default = pkgs.mkShell {
        packages = [ pkgs.lean4 ];
      };

      packages.${system}.default = pkgs.stdenvNoCC.mkDerivation {
        pname = "ppa-lean";
        version = "0.1.0";
        src = self;
        nativeBuildInputs = [ pkgs.lean4 ];
        buildPhase = ''
          export HOME="$TMPDIR/home"
          mkdir -p "$HOME"
          lake build
        '';
        installPhase = ''
          mkdir -p "$out"
          cp -r .lake/build/lib "$out/lib"
        '';
      };

      checks.${system}.default = self.packages.${system}.default;
    };
}
