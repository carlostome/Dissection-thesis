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

main :: IO ()
main = shakeArgs shakeOptions $ do
  want ["thesis"]

  phony "thesis" $ do
    need ["thesis/main" <.> pdf]

  phony "paper" $ do
    need ["paper/main" <.> pdf]

  phony "distclean" $ do
    need ["clean-paper" , "clean-thesis"]

  -- thesis rules
  "thesis/main" <.> pdf %> \out -> do
    let files = [ "thesis" </> file <.> tex | file <- thesis_lagda_files]
        bib   = "thesis/main.bib"
        fmt   = "thesis/thesis.fmt"
        sty   = "thesis/agda.sty"
    need (bib : fmt : sty : files)
    cmd_ "latexmk -f -pdf -cd -xelatex thesis/main.tex"

  -- paper rules
  "paper/main" <.> tex %> \out -> do
    let input      = out -<.> lagda
        dir        = takeDirectory out
        preamble   = "preamble" <.> tex
        fmtFiles   = [ "paper" </> file <.> fmt | file <- paper_fmt_files]
          where paper_fmt_files = [ "paper" , "intro" , "generic" ]
        sty        = "paper/agda.sty"
    need $ [input , sty , dir </> "preamble" <.> tex ] ++ fmtFiles
    cmd_ (Cwd dir) "lhs2TeX --agda -o" [takeFileName out] (takeFileName input)

  "paper/main" <.> pdf %> \out -> do
    putNormal "Building paper"
    let main       = out -<.> tex
        figures    = [ "paper" </> "figures" </> ("figure" ++ show n) <.> "tex" 
                     | n <- [1..4]]
        bib        = "paper/main.bib"
    need $ [main , bib] ++ figures
    cmd_ "latexmk -f -pdf -cd paper/main.tex"

  -- cleaning
  phony "clean-paper" $ do
    putNormal "Cleaning files in paper"
    cmd_ "latexmk -C -cd paper/main.tex"
    removeFilesAfter "paper" ["main.tex", "*.bbl", "main.pdf", "main.ptb"]

  phony "clean-thesis" $ do
    return ()
    -- putNormal "Cleaning files in thesis"
    -- cmd_ "latexmk -c -cd thesis/main.tex"
    -- removeFilesAfter "thesis" ["*.tex", "*.bbl"]

