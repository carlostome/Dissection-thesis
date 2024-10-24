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

thesis_lagda_files = [ "main"      , "introduction" 
                     , "background", "expression"
                     , "generic"   , "conclusion" ]

main :: IO ()
main = shakeArgs shakeOptions $ do
  want ["thesis"]

  phony "thesis" $ do
    need ["thesis/main" <.> pdf]

  phony "paper" $ do
    need ["paper/main" <.> pdf]

  phony "presentation" $ do
    need ["presentation/main" <.> pdf]

  phony "tyde18-presentation" $ do
    need ["tyde18-presentation/main" <.> pdf]

  phony "chalmers-presentation" $ do
    need ["chalmers-presentation/main" <.> pdf]

  phony "distclean" $ do
    need ["clean-paper" , "clean-thesis"]

  phony "formal" $ do
    cmd_ (Cwd "src") "agda Regular.agda"

  -- thesis rules
  "thesis/*.tex" %> \out -> do
    let input     = out -<.> lagda
        dir       = takeDirectory out
        fmtFile   = out -<.> fmt
    need [input , fmtFile]
    cmd_ (Cwd dir) "lhs2TeX --agda -o" [takeFileName out] (takeFileName input)

  "thesis/main" <.> pdf %> \out -> do
    let files = [ "thesis" </> file <.> tex | file <- thesis_lagda_files]
        bib   = "thesis/main.bib"
        sty   = "thesis/agda.sty"
        figures    = [ "thesis" </> "figures" </> ("figure" ++ show n) <.> tex
                     | n <- [1..5]]
    need (bib : sty : files ++ figures)
    cmd_ "latexmk -f -xelatex -pdf -cd thesis/main.tex"

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

  -- presentation
  "presentation/main" <.> tex %> \out -> do
    putNormal "Building presentation"
    let input  = out -<.> lagda
        dir    = takeDirectory out
        figures    = [ "presentation" </> "figures" </> ("figure" ++ show n) <.> "tex" 
                     | n <- [1..6]]
    need $ [input, "presentation/presentation.fmt"] ++ figures
    cmd_ (Cwd dir) "lhs2TeX --agda -o" [takeFileName out] (takeFileName input)

  "presentation/main" <.> pdf %> \out -> do
    putNormal "Building presentation"
    let main  = out -<.> tex
    need [main]
    cmd_ "latexmk -xelatex -pdf -cd presentation/main.tex"

  -- tyde presentation
  "tyde18-presentation/main" <.> tex %> \out -> do
    putNormal "Building presentation"
    let input  = out -<.> lagda
        dir    = takeDirectory out
        figures    = [ "tyde18-presentation" </> "figure" <.> "tex" ]
    need $ [input, "tyde18-presentation/presentation.fmt"] ++ figures
    cmd_ (Cwd dir) "lhs2TeX --agda -o" [takeFileName out] (takeFileName input)

  "tyde18-presentation/main" <.> pdf %> \out -> do
    putNormal "Building presentation"
    let main  = out -<.> tex
    need [main]
    cmd_ "latexmk -xelatex -pdf -cd tyde18-presentation/main.tex"

  -- chalmers presentation
  "chalmers-presentation/main" <.> tex %> \out -> do
    putNormal "Building presentation"
    let input  = out -<.> lagda
        dir    = takeDirectory out
        figures    = [ "chalmers-presentation" </> "figure" <.> "tex" ]
    need $ [input, "chalmers-presentation/presentation.fmt"] ++ figures
    cmd_ (Cwd dir) "lhs2TeX --agda -o" [takeFileName out] (takeFileName input)

  "chalmers-presentation/main" <.> pdf %> \out -> do
    putNormal "Building presentation"
    let main  = out -<.> tex
    need [main]
    cmd_ "latexmk -xelatex -pdf -cd chalmers-presentation/main.tex"

  -- cleaning
  phony "clean-paper" $ do
    putNormal "Cleaning files in paper"
    cmd_ "latexmk -C -cd paper/main.tex"
    removeFilesAfter "paper" ["comment.cut", "main.tex", "*.bbl", "main.ptb"]

  phony "clean-thesis" $ do
    putNormal "Cleaning files in paper"
    cmd_ "latexmk -C -cd thesis/main.tex"
    removeFilesAfter "thesis" $ ["*.bbl", "main.pdf", "main.ptb"]
                              ++ map (<.> tex) thesis_lagda_files

  phony "clean-presentation" $ do
    putNormal "Cleaning files in paper"
    cmd_ "latexmk -C -cd chalmers-presentation/main.tex"
    removeFilesAfter "chalmers-presentation" 
      ["main.tex", "*.bbl", "main.pdf", "main.ptb" , "main.nav", "main.snm"]
