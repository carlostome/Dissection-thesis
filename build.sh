nix-shell -p "haskell.packages.ghc822.ghcWithPackages (pkgs: [pkgs.shake
pkgs.lhs2tex])" --command "runhaskell Shake.hs $1"
