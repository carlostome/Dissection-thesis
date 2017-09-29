# Proposal --------------------

SRC := src

PROPOSAL_AGDA_MODULES := $(SRC)/Proposal
PROPOSAL_TEX          := main introduction literature
PROPOSAL_AGDA         := $(wildcard $(PROPOSAL_AGDA_MODULES)/*.agda)

proposal: proposal/main.pdf

snippets-dir:
	mkdir -p snippets

$(PROPOSAL_AGDA): snippets-dir
	./scripts/gen-snippets.sh gen_snippets $@ snippets $(SRC)

proposal/%.tex: proposal/%.lagda $(PROPOSAL_AGDA)
	lhs2TeX --agda -o $@ $<

proposal/main.pdf: $(PROPOSAL_TEX:%=proposal/%.tex) proposal/main.bib
	cd proposal; latexmk -pdf -xelatex -outdir=out main.tex
	cp proposal/out/main.pdf proposal/main.pdf
	rm proposal/out/main.pdf

cleanproposal:
	rm -rf snippets
	rm -rf proposal/out
	rm -rf $(PROPOSAL_TEX:%=proposal/%.tex)
	rm -rf proposal/literature.rel
