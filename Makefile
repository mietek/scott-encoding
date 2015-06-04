.PHONY: all agda coq haskell idris
all: agda coq haskell idris

.PHONY: clean agda-clean coq-clean haskell-clean idris-clean
clean: agda-clean coq-clean haskell-clean idris-clean


agda := $(wildcard agda-explicit/*.agda) $(wildcard agda-implicit/*.agda)
agdai := $(patsubst %.agda,%.agdai,$(agda))

agda: $(agdai)

%.agdai: %.agda
	agda -i /usr/local/Cellar/agda/2.4.2.2_1/agda-stdlib/src -i $(@D) $< | grep -v Skipping

agda-clean:
	rm -rf $(agdai)


v := $(wildcard coq-explicit/*.v) $(wildcard coq-implicit/*.v)
vo := $(patsubst %.v,%.vo,$(v))
glob := $(patsubst %.v,%.glob,$(v))

coq: $(vo)

%.vo: %.v
	coqtop -compile $(patsubst %.v,%,$<)

coq-clean:
	rm -rf $(vo) $(glob)


hs := $(wildcard haskell/*.hs)
hi := $(patsubst %.hs,%.hi,$(hs))
o := $(patsubst %.hs,%.o,$(hs))

haskell: $(hi)

%.hi: %.hs
	ghc -Wall $<

haskell-clean:
	rm -rf $(hi) $(o)


idr := $(wildcard idris-explicit/*.idr) $(wildcard idris-implicit/*.idr)
ibc := $(patsubst %.idr,%.ibc,$(idr))

idris: $(ibc)

%.ibc: %.idr
	idris --check $<

idris-clean:
	rm -rf $(ibc)
