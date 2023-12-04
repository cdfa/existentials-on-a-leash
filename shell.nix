{ pkgs ? import <nixpkgs> { } }:
pkgs.mkShell
{
  buildInputs = with pkgs; [
    (haskellPackages.ghcWithPackages
      (p: with p; [
        lens
      ]))
    cabal-install
    hlint
    ghcid
    haskell-language-server
    rnix-lsp
    (pkgs.writeShellScriptBin
      "build"
      "${haskellPackages.unlit}/bin/unlit --to=backtickfence --language=haskell --input=existentials-on-a-leash.lhs | ${pkgs.gnused}/bin/sed 's/^\\\\#/#/' > existentials-on-a-leash.md")
  ] ++ (with haskellPackages; [
    apply-refact
    floskell
  ]);
}
