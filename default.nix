{ pkgs ? (import <nixpkgs> {}).pkgs
}:
let
  myemacs =
    with pkgs.emacsPackages; with pkgs.emacsPackagesNg; pkgs.emacsWithPackages
      [ org paredit haskellMode magit ];
  tex = pkgs.texlive.combine {
    inherit (pkgs.texlive)
      beamer bussproofs capt-of cm-super framed ifplatform marvosym minted
      scheme-small wasysym wrapfig xstring xcolor;
  };
  myhaskell = pkgs.haskellPackages.ghcWithPackages (p: with p;
    [ base ]);
in with pkgs; stdenv.mkDerivation {
  name = "proplcf";
  buildInputs = [ myemacs myhaskell tex pythonPackages.pygments ];
}
