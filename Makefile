TARGET = main.byte

default: $(TARGET)

hard: test

%.byte: $(wildcard *.ml)
	corebuild $@

STLCS = $(wildcard tests/*.stlc)
OUTS  = $(subst .stlc,.out,$(STLCS))
TESTS = $(subst .stlc,.test,$(STLCS))

%.test: %.stlc $(TARGET)
	./$(TARGET) < $*.stlc | diff $*.out -

test: $(TESTS)

%.out: %.stlc $(TARGET)
	./$(TARGET) < $< > $@

reset_regression_tests: $(OUTS)

clean:
	$(RM) -R *.byte *.native _build

