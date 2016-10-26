{ pkgs ? (import <nixpkgs> {}).pkgs
}:
let
  myemacs =
    with pkgs.emacsPackages; with pkgs.emacsPackagesNg; pkgs.emacsWithPackages
      [ org paredit haskellMode magit ];
  myhaskell = pkgs.haskellPackages.ghcWithPackages (p: with p;
    [ base ]);
in with pkgs; stdenv.mkDerivation {
  name = "meta";
  buildInputs = [ myemacs myhaskell ];
}
