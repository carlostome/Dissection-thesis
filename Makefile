SRC := src

PROPOSAL_MODULES      := Proposal
PROPOSAL_TEX          := main introduction literature
PROPOSAL_AGDA         := $(shell find $(SRC)/$(PROPOSAL_MODULES)/ -type f -name '*.lagda')

proposal: proposal/main.pdf

src-tex:
	mkdir -p src-tex

src-tex/%.tex: $(SRC)/%.lagda
	agda -i $(SRC) --latex-dir=src-tex --latex --allow-unsolved-metas --no-termination-check $<

proposal/%.tex: proposal/%.lagda
	lhs2TeX --agda -o $@ $<

proposal/main.pdf: $(PROPOSAL_TEX:%=proposal/%.tex) $(PROPOSAL_AGDA:$(SRC)/%.lagda=src-tex/%.tex) proposal/main.bib proposal.fmt | src-tex
	cp src-tex/agda.sty proposal
	cd proposal; latexmk -pdf -xelatex -outdir=out main.tex
	cp proposal/out/main.pdf proposal/main.pdf
	rm proposal/out/main.pdf

cleanproposal:
	rm -rf src-tex
	rm  proposal/agda.sty
	rm -rf proposal/out
	rm -rf $(PROPOSAL_TEX:%=proposal/%.tex)
	rm -rf proposal/literature.rel
