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

-- fmt file extension
fmt :: FilePath
fmt = "fmt"

-- lagda files used to build the thesis
thesis_lagda_files :: [String]
thesis_lagda_files = [ "main" , "tree" , "problem" , "background"]

-- lagda files used for the paper
paper_lagda_files :: [String]
paper_lagda_files = [ "main" ]

paper_fmt_files :: [String]
paper_fmt_files = [ "paper" , "intro" , "generic" ]

main :: IO ()
main = shakeArgs shakeOptions $ do
  want ["thesis"]

  phony "distclean" $ do
    putNormal "Cleaning files in thesis"
    cmd_ "latexmk -c -cd thesis/main.tex"
    removeFilesAfter "thesis" ["*.tex", "*.bbl"]

    putNormal "Cleaning files in paper"
    cmd_ "latexmk -c -cd paper/main.tex"
    removeFilesAfter "paper" ["*.tex", "*.bbl"]

  phony "thesis" $ do
    need ["thesis/main" <.> pdf]

  phony "paper" $ do
    need ["paper/main" <.> pdf]

  "//*.tex" %> \out -> do
    let input = out -<.> lagda
        dir   = takeDirectory out
    putNormal $ "Building " ++ out ++ " from " ++ input ++ " in " ++ dir
    need [input]
    cmd_ (Cwd dir) "lhs2TeX --agda -o" [takeFileName out] (takeFileName input)

  "thesis/main" <.> pdf %> \out -> do
    let files = [ "thesis" </> file <.> tex | file <- thesis_lagda_files]
        bib   = "thesis/main.bib"
        fmt   = "thesis/thesis.fmt"
        sty   = "thesis/agda.sty"
    need (bib : fmt : sty : files)
    cmd_ "latexmk -pdf -cd -xelatex thesis/main.tex"

  "paper/main" <.> pdf %> \out -> do
    putNormal "Building paper"
    let files      = [ "paper" </> file <.> tex | file <- paper_lagda_files]
        bib        = "paper/main.bib"
        fmtFiles   = [ "paper" </> file <.> fmt | file <- paper_fmt_files]
        sty        = "paper/agda.sty"
    need (bib : sty : (files ++ fmtFiles))
    cmd_ "latexmk -pdf -cd paper/main.tex"
