import Development.Shake
import Development.Shake.Command
import Development.Shake.FilePath
import Development.Shake.Util

-- pdf file extension
pdf :: FilePath
pdf = "pdf"

-- lagda file extension
lagda :: FilePath
lagda = "lagda"

-- tex file extension
tex :: FilePath
tex = "tex"

-- lagda modules used to build the thesis
thesis_lagda_modules :: [String]
thesis_lagda_modules = [ "main" , "tree" , "problem" , "background"]

main :: IO ()
main = shakeArgs shakeOptions $ do
  want ["thesis/main" <.> pdf]

  phony "distclean" $ do
    putNormal "Cleaning files in thesis"
    cmd_ "latexmk -c -cd thesis/main.tex"
    removeFilesAfter "thesis" ["*.tex", "*.bbl"]

  "thesis/*.tex" %> \out -> do
    let inp = out -<.> lagda
    need [inp]
    cmd_ (Cwd "thesis") "lhs2TeX --agda -o" [takeFileName out] (takeFileName inp)

  "thesis/main" <.> pdf %> \out -> do
    let mods = [ "thesis" </> f <.> tex | f <- thesis_lagda_modules]
        bib  = "thesis/main.bib"
        fmt  = "thesis/thesis.fmt"
        sty  = "thesis/agda.sty"
    need (bib : fmt : sty : mods)
    cmd_ "latexmk -pdf -cd -xelatex thesis/main.tex"
