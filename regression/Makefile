DEBUG_FILES=stack-dump-before data-dump-before extra-roots-dump-before heap-dump-before stack-dump-after data-dump-after extra-roots-dump-after heap-dump-after
TESTS=$(sort $(filter-out test111, $(basename $(wildcard test*.lama))))

LAMAC=../src/lamac

.PHONY: check $(TESTS)


check: ctest111 $(TESTS)
	sort -o typecheck.log typecheck.log

$(TESTS): %: %.lama
	@echo "regression/$@"
	@cat $@.input | LAMA=../runtime $(LAMAC) -i $< > $@.log && diff $@.log orig/$@.log
	@cat $@.input | LAMA=../runtime $(LAMAC) -ds -s $< > $@.log && diff $@.log orig/$@.log
	@LAMA=../runtime $(LAMAC) $< && cat $@.input | ./$@ > $@.log && diff $@.log orig/$@.log
	-LAMA=../runtime timeout 2s $(LAMAC) -t $< >/dev/null \
		&& printf "done\t$<\n" >> typecheck.log \
		|| printf "fail\t$<\n" >> typecheck.log

ctest111:
	@echo "regression/test111"
	@LAMA=../runtime $(LAMAC) test111.lama && cat test111.input | ./test111 > test111.log && diff test111.log orig/test111.log

clean:
	$(RM) test*.log *.s *.sm *~ $(TESTS) *.i $(DEBUG_FILES) test111 typecheck.log
	$(MAKE) clean -C expressions
	$(MAKE) clean -C deep-expressions
