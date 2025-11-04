.PHONY: test dist

Vsim: Vsim.c
	gcc -Wall -Werror -o $@ $<

test: Vsim
	./Vsim sample.txt
	diff -w -B --color=auto simulation.txt sample_simulation.txt

dist: Vsim.c.txt

Vsim.c.txt: Vsim.c
	cp $< $@
