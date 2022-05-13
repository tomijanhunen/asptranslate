# Translation-Based ASP Tools under ASPTOOLS

TOOLS=		acyc2solver lp2acyc lp2normal lp2normal2 lp2sat \
		lpreify support unsat2lp
ACYC=		acyc.o
CTR=		counter.o
NORMAL=		prime.o condflags.o expression.o
PRIM=		primitives.o
SCC=		scc.o

LPLIB=		../../asplib

INC=		$(LPLIB)/liblp
LIB=		$(LPLIB)/liblp/lib
BIN=		../bin

CC=		gcc
CCFLAGS=	-g -I$(INC)

LDFLAGS=	-static -L$(LIB) -llp

all: 		$(TOOLS)

acyc2solver:	$(ACYC) $(SCC) acyc2solver.o
		$(CC) $(ACYC) $(SCC) acyc2solver.o -o acyc2solver $(LDFLAGS)

lp2acyc:	$(ACYC) $(SCC) lp2acyc.o
		$(CC) $(ACYC) $(SCC) lp2acyc.o -o lp2acyc $(LDFLAGS)

lp2normal:	lp2normal.o
		$(CC) lp2normal.o -o lp2normal $(LDFLAGS)

lp2normal2:	$(NORMAL) lp2normal2.o
		$(CC) $(NORMAL) lp2normal2.o -o lp2normal2 $(LDFLAGS) -lm

lp2sat:		$(ACYC) $(SCC) lp2sat.o
		$(CC) $(ACYC) $(SCC) lp2sat.o -o lp2sat $(LDFLAGS)

lpreify:	$(PRIM) $(SCC) lpreify.o
		$(CC) $(PRIM) $(SCC) lpreify.o -o lpreify $(LDFLAGS)

support:	support.o
		$(CC) support.o -o support $(LDFLAGS)

unsat2lp:	unsat2lp.o
		$(CC) unsat2lp.o -o unsat2lp $(LDFLAGS)

clean:
		rm -f *.o
		rm -f $(TOOLS)

install:	$(TOOLS)
		for t in $(TOOLS);\
		do cp -f ./$$t $(BIN)/$$t;\
		   strip $(BIN)/$$t; done

%.o:            %.c
		$(CC) $(CCFLAGS) -c $*.c
