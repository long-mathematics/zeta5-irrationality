.PHONY: lean audit verify pdf check

lean:
	lake build

audit:
	python3 -B -m unittest discover -s scripts -p 'test_*.py'
	python3 -B scripts/audit_lean.py

verify:
	python3 certificates/verify.py

pdf:
	cd paper && latexmk -pdf -interaction=nonstopmode -halt-on-error zeta5_formalization_draft.tex

check: audit verify lean
