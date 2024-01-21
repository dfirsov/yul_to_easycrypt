TIMEOUT ?= 10

PROOF_FILES = $(wildcard proofs/*.ec)
PROOF_FILES = $(wildcard proofs/*/*.ec)

EASYCRYPT ?= easycrypt
ECARGS ?=

default : check_all

# Check all EasyCrypt proofs
check_all : $(PROOF_FILES:.ec=.eco)

%.eco : %.ec $(PROOF_FILES)
	echo Checking "$<"
	$(EASYCRYPT) $(ECARGS) -p "CVC4" -p "Z3" -p "Alt-Ergo" -I "proofs/" -I "proofs/auxiliary_lemmas" -I "proofs/montgomery_arithmetic" -I "proofs/ecAdd" -I "proofs/modular_inversion"  -timeout "$(TIMEOUT)" "$<"




