{
  inputs = {
    utils.url = "github:numtide/flake-utils";
  };
  outputs = { self, nixpkgs, utils }: utils.lib.eachDefaultSystem (system:
    let
      pkgs = nixpkgs.legacyPackages.${system};
    in
    {
      devShell = pkgs.mkShell {
        buildInputs = with pkgs; [
          haskell.compiler.ghc912
          cabal-install
          haskell.packages.ghc912.cabal-gild
          haskell.packages.ghc912.haskell-language-server
          fourmolu
          hlint
        ];
      };
    }
  );
}
