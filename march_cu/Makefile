#CLAGS	=	-std=c99 -O3 -static -fno-strict-aliasing -Wall
#CFLAGS	=	-O3 -static -fno-strict-aliasing -Wall -DNDEBUG
#CFLAGS	=	-Wall -ggdb -pg
CFLAGS	=	-O3 -fno-strict-aliasing -Wall -DNDEBUG

CC	= 	gcc

.c.o:
		$(CC) -c $(CFLAGS) $(SATTEST) -o $@ $<

march_cu: march.o \
		cube.o \
		distribution.o \
		doublelook.o \
		equivalence.o \
		memory.o \
		microsat.o \
		lookahead.o \
		parser.o \
		preselect.o \
		progressBar.o \
		resolvent.o \
		solver.o \
		tree.o
		$(CC) $(CFLAGS) $(SATTEST) *.o -lm -o march_cu

march.o: march.c \
		march.h \
		common.h \
		distribution.h \
		parser.h \
		solver.h \
		preselect.h \
		progressBar.h

resolvent.o: resolvent.c \
		resolvent.h \
		common.h \
		lookahead.h \
		memory.h

distribution.o: distribution.c \
		distribution.h \
		common.h

doublelook.o: doublelook.c \
		doublelook.h \
		common.h

equivalence.o: equivalence.c \
		equivalence.h \
		memory.h

memory.o: memory.c \
		memory.h \
		common.h

cube.o: cube.c \
		cube.h \
		common.h

parser.o: parser.c \
		parser.h \
		common.h \
		equivalence.h

solver.o: solver.c \
		solver.h \
		common.h \
		lookahead.h \
                microsat.h \
		preselect.h \
		progressBar.h

microsat.o: microsat.c \
		microsat.h

preselect.o: preselect.c \
		preselect.h \
		common.h

tree.o: tree.c \
		tree.h

lookahead.o: lookahead.c \
		lookahead.h \
		doublelook.h \
		common.h \
		tree.h \
		solver.h

progressBar.o: progressBar.c \
		progressBar.h \
		common.h

clean:
	rm *.o march_cu
