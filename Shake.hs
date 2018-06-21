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
  "thesis/*.tex" %> \out -> do
    let input     = out -<.> lagda
        dir       = takeDirectory out
        fmtFile   = out -<.> fmt
    need [input , fmtFile]
    cmd_ (Cwd dir) "lhs2TeX --agda -o" [takeFileName out] (takeFileName input)

  "thesis/main" <.> pdf %> \out -> do
    let files = [ "thesis" </> file <.> tex | file <-lagda_files]
                  where lagda_files = [ "main"      , "introduction" 
                                      , "background", "expression"
                                      , "generic"   , "conclusion" ]
        bib   = "thesis/main.bib"
        sty   = "thesis/agda.sty"
        figures    = [ "thesis" </> "figures" </> ("figure" ++ show n) <.> "tex" 
                     | n <- [1..5]]
    need (bib : sty : files ++ figures)
    cmd_ "latexmk -f -pdf -cd thesis/main.tex"

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
    putNormal "Cleaning files in paper"
    cmd_ "latexmk -C -cd thesis/main.tex"
    removeFilesAfter "thesis" ["*.tex", "*.bbl", "main.pdf", "main.ptb"]
