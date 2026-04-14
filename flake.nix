{
  inputs = {
    utils.url = "github:numtide/flake-utils";
  };
  outputs = { self, nixpkgs, utils }: utils.lib.eachDefaultSystem (system:
    let
      pkgs = nixpkgs.legacyPackages.${system};
      ghcName = "ghc912";
      haskellPackages = pkgs.haskell.packages.${ghcName};
    in
    {
      devShell = pkgs.mkShell {
        buildInputs = with pkgs; [
          haskell.compiler.${ghcName}
          cabal-install
          haskellPackages.cabal-gild
          haskellPackages.haskell-language-server
          fourmolu
          hlint
        ];
      };
    }
  );
}
