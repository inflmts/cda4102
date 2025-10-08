.PHONY: test dist

Vsim: Vsim.c
	gcc -Wall -Werror $< -o $@

test: Vsim
	./Vsim sample.txt
	diff -w -B --color=auto disassembly.txt sample_disassembly.txt
	diff -w -B --color=auto simulation.txt sample_simulation.txt

dist: /tmp/Vsim.c.txt
/tmp/Vsim.c.txt: Vsim.c
	cp $< $@
