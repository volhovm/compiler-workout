TESTS=$(basename $(sort $(wildcard test*.expr)))

RC=../src/rc.opt

.PHONY: check $(TESTS) 

check: $(TESTS)

$(TESTS): %: %.expr
	@echo "Testing interpreter"
	@cat $@.input | $(RC) -i $< > $@.log && diff -u orig/$@.log $@.log 
	@echo "Testing SM"
	@cat $@.input | $(RC) -s $< > $@.log && diff -u orig/$@.log $@.log 
#	@$(RC) $< && cat $@.input | ./$@ > $@.log && diff $@.log orig/$@.log

clean:
	rm -f test*.log *.s *~ $(TESTS)
#	find deep-expressions/ expressions/ -type f -name "generated*" -and ! -name "*.*" -exec rm {} \;
