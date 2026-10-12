PYTHON ?= python3

.PHONY: verify verify-large paper clean
verify:
	$(PYTHON) verification/check_sources.py
	$(PYTHON) verification/replay.py
	$(PYTHON) verification/independent_content.py
	$(PYTHON) verification/independent_functional.py

verify-large:
	$(PYTHON) verification/replay.py --large

paper:
	cd paper && pdflatex -interaction=nonstopmode -halt-on-error main.tex
	cd paper && pdflatex -interaction=nonstopmode -halt-on-error main.tex

clean:
	rm -f paper/main.aux paper/main.log paper/main.out paper/main.toc
