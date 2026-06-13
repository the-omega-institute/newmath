PDF=main.pdf
PARTS=$(wildcard parts/*.tex)

.PHONY: all precheck check clean

all: precheck $(PDF)

$(PDF): main.tex $(PARTS)
	pdflatex -interaction=nonstopmode -halt-on-error main.tex
	pdflatex -interaction=nonstopmode -halt-on-error main.tex

precheck: main.tex $(PARTS)
	@for f in $(PARTS); do \
	  lines=$$(wc -l < "$$f"); \
	  if [ "$$lines" -gt 800 ]; then \
	    echo "$$f has $$lines lines, above the 800-line limit"; \
	    exit 1; \
	  fi; \
	done
	@if grep -R "\\\\leanchecked\\|\\\\leanstmt\\|\\\\leanvariant\\|\\\\leansorryd\\|\\\\leandef\\|\\\\leantarget" main.tex $(PARTS) >/dev/null 2>&1; then \
	  echo "Lean marker macro found in FibonacciReality paper"; \
	  exit 1; \
	fi
	@if grep -R "\\\\\\[\\|\\\\\\]\\|\\\\begin{equation}\\|\\\\begin{equation\\*}\\|\\\\begin{align}\\|\\\\begin{align\\*}\\|\\\\begin{eqnarray}\\|\\\\begin{eqnarray\\*}" main.tex $(PARTS) >/dev/null 2>&1; then \
	  echo "Forbidden display math environment found"; \
	  exit 1; \
	fi
	@if grep -R "[一-龥]" main.tex $(PARTS) >/dev/null 2>&1; then \
	  echo "Chinese text found inside FibonacciReality paper body"; \
	  exit 1; \
	fi

check: precheck
	pdflatex -draftmode -interaction=nonstopmode -halt-on-error main.tex

clean:
	rm -f main.aux main.log main.out main.pdf main.toc
