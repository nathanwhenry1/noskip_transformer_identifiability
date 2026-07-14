.PHONY: build audit imports axioms check

build:
	lake build

audit:
	python3 scripts/check_no_placeholders.py AnyLayerIdentifiabilityProof AnyLayerIdentifiabilityProof.lean --json source-audit.json

imports:
	python3 scripts/check_local_imports.py . AnyLayerIdentifiabilityProof

axioms:
	./scripts/print_axioms.sh 2>&1 | tee axiom-report.txt
	python3 scripts/check_axioms.py axiom-report.txt

check: imports audit build axioms
