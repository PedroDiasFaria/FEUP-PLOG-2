:-use_module(library(clpfd)).
:-use_module(library(lists)).
:-use_module(library(random)).

%%%%%%%%%%%%%%%%%%%%%%%%
%      EASY AS SUM     %
%%%%%%%%%%%%%%%%%%%%%%%%

%TRABALHO REALIZADO POR:
%Pedro Faria	-	ei11167
%Rui Figueira	-	ei11021

%0 Interface
draw_empty_line(0):-write('-'),nl.
draw_empty_line(N):-write('--'), N1 is N-1, draw_empty_line(N1).

draw_line([]).
draw_line([H|T]):- 	write('|'), 
					((H =:= 0) -> 	write(' ');
									write(H)
					) ,
					draw_line(T).

draw_lines(_, 0, _).
draw_lines([H|T], N, GSize):- draw_line(H), write('|'), nl, draw_empty_line(GSize), N2 is N-1, draw_lines(T,N2, GSize).

draw_grid(Grid, GSize):- draw_empty_line(GSize), draw_lines(Grid, GSize, GSize).

%1 Decl Vars

%Restricoes a efetuar na grelha

%Restricoes do enunciado
sumTop(		[9,  0, 10, 6, 0, 7, 9], 1).
sumRight(	[0, 11,  6, 6, 6, 0, 9], 1).
sumBottom(	[5,  0,  5, 8, 0, 9, 9], 1).
sumLeft(	[0,  7, 11, 8, 4, 0, 0], 1).

%Restricoes 5x5
sumTop( 	[7, 6, 4, 7, 3], 2).
sumRight(	[5, 5, 5, 5, 5], 2).
sumBottom(	[3, 4, 6, 3, 7], 2).
sumLeft(	[5, 5, 5, 5, 5], 2).

%Solucao 2
% 3 | 4 | 1 |   | 2
% 1 | 3 | 2 | 4 |
% 2 |   | 4 | 1 | 3
%   | 1 | 3 | 2 | 4
% 4 | 2 |   | 3 | 1

%Todas as restricoes preenchidas
sumTop( 	[3, 11, 11,  4, 11, 11,  8,  3], 3).
sumRight(	[3,  5, 11, 11,  7, 11, 11,  3], 3).
sumBottom(	[7,  8,  7, 10,  7,  7,  6, 12], 3).
sumLeft(	[9, 13,  9,  9,  7,  5,  7,  9], 3).

%1 restricao nula
sumTop( 	[3, 11, 11,  4, 11, 11,  8,  3], 4).
sumRight(	[3,  5, 11, 11,  7, 11, 11,  3], 4).
sumBottom(	[7,  8,  7, 10,  7,  7,  0, 12], 4).
sumLeft(	[9, 13,  9,  9,  7,  5,  7,  9], 4).

%2 restricoes nulas
sumTop( 	[3,  0, 11,  4, 11, 11,  8,  3], 5).
sumRight(	[3,  5, 11, 11,  7, 11, 11,  3], 5).
sumBottom(	[7,  8,  7, 10,  7,  7,  0, 12], 5).
sumLeft(	[9, 13,  9,  9,  7,  5,  7,  9], 5).

%6 restricoes nulas
sumTop( 	[3,  0, 11,  4, 11, 11,  8,  3], 6).
sumRight(	[3,  5, 11, 11,  7,  0, 11,  0], 6).
sumBottom(	[7,  0,  7, 10,  7,  7,  0, 12], 6).
sumLeft(	[9, 13,  0,  9,  7,  5,  7,  9], 6).


%2 Decl Dominios
gridSize([],0).
gridSize([_|L],N) :- gridSize(L,N1), N is N1 + 1.

len_row([],_).
len_row([L|T],NumberCol):-
						length(L,NumberCol),    % define o numero de celulas de cada linha da grelha final
						len_row(T,NumberCol).

%Dominio: [0 - Tamanho-1]
%Exempl: Grelha 7x7, tem dominio [0-6]
put_domain_row(_, _, 0).
put_domain_row([H|T], UpperLimit, N):- N > 0,
									domain(H, 0, UpperLimit),
									N1 is N-1,
									put_domain_row(T, UpperLimit, N1).


put_domains(Sol, Gridsize):- UpperLimit is Gridsize-1,
							N is Gridsize,
							put_domain_row(Sol, UpperLimit, N).


%3 Decl Restricoes
%Um numero nao se pode repetir em cada linha
put_distinct_line(_, Gridsize, N):- N > Gridsize.
put_distinct_line([H|T], Gridsize, N):-
							all_distinct(H),
							N1 is N + 1,
							put_distinct_line(T, Gridsize, N1).

put_distinct(Sol, Gridsize):-put_distinct_line(Sol, Gridsize, 1),
							transpose(Sol, SolTransp),
							put_distinct_line(SolTransp, Gridsize, 1).

put_restrictions_line([], _, _,_,_).
put_restrictions_line([H|T], Gridsize, [SumRH|SumRT],[SumLH|SumLT], N):-
								element(1, H, FirstInRow),
								element(Gridsize, H, LastInRow),

								element(2, H, SecondInRow),
								SecondLastIndex is Gridsize -1,
								element(SecondLastIndex, H, SecondLastInRow),

								element(3, H, ThirdInRow),
								ThirdLastIndex is Gridsize -2,
								element(ThirdLastIndex, H, ThirdLastInRow),

								(SumRH #= 0) #\/(
								(SumRH #> 0) #/\ 
									(
									(((FirstInRow #> 0) #/\ (LastInRow #> 0)) #/\ (SumRH #= FirstInRow + LastInRow))
									#\/
									(((FirstInRow #= 0) #/\ (SecondInRow #> 0) #/\ (LastInRow #> 0)) #/\ (SumRH #= SecondInRow + LastInRow))
									#\/
									(((FirstInRow #> 0) #/\ (SecondInRow #> 0) #/\ (LastInRow #= 0)) #/\ (SumRH #= FirstInRow + SecondLastInRow))
									)
									),

								(SumLH #= 0) #\/(
								(SumLH #> 0) #/\
									(
									(((FirstInRow #> 0) #/\ (LastInRow #> 0) #/\ (SecondInRow #> 0) #/\ (SecondLastInRow #> 0)) #/\ (SumLH #= SecondInRow + SecondLastInRow))
									#\/
									(((FirstInRow #> 0) #/\ (LastInRow #> 0) #/\ (SecondInRow #= 0) #/\ (SecondLastInRow #> 0)) #/\ (SumLH #= ThirdInRow + SecondLastInRow))
									#\/
									(((FirstInRow #> 0) #/\ (LastInRow #> 0) #/\ (SecondInRow #> 0) #/\ (SecondLastInRow #= 0)) #/\ (SumLH #= SecondInRow + ThirdLastInRow))
									#\/
									(((FirstInRow #= 0) #/\ (LastInRow #> 0) #/\ (SecondInRow #> 0) #/\ (SecondLastInRow #> 0) #/\ (ThirdInRow #> 0)) #/\ (SumLH #= ThirdInRow + SecondLastInRow))
									#\/
									(((FirstInRow #> 0) #/\ (LastInRow #= 0) #/\ (SecondInRow #> 0) #/\ (SecondLastInRow #> 0) #/\ (ThirdLastInRow #> 0)) #/\ (SumLH #= SecondInRow + ThirdLastInRow))
									)
									),
	
							N1 is N+1,
							put_restrictions_line(T, Gridsize, SumRT, SumLT, N1).

							
put_restrictions(Sol, Gridsize, SumT, SumR, SumB, SumL):-
							put_restrictions_line(Sol, Gridsize, SumR, SumL, 1),
							transpose(Sol, Sol2),
							put_restrictions_line(Sol2, Gridsize, SumT, SumB, 1).

%4 Pesq Solucao

%Ex é o numero do exemplo definido nas declaracoes acima
%Para pesquisar a solucao do enunciado: easyAsSum(Sol, 1).
easyAsSum(Sol, Ex):-
				sumTop(SumT, Ex), sumRight(SumR, Ex), sumBottom(SumB, Ex),sumLeft(SumL, Ex),								%Inicializacao das listas de restricao
				gridSize(SumT, Gridsize),gridSize(SumR, Gridsize),gridSize(SumB, Gridsize),gridSize(SumL, Gridsize),		%Confirmar que ha o mesmo numero de elementos nas listas de restricao

				nl,nl,write('------E A S Y   A S   S U M------'),
				nl,nl,write('Grid: '),write(Gridsize),write('x'),write(Gridsize),nl,nl,

				length(Sol, Gridsize),																						%Lista com o tamanho da grelha final
				len_row(Sol, Gridsize),																						%Numero de listas de listas igual ao tamanho da grelha final 
				put_domains(Sol, Gridsize),																					%Colocar dominios
				put_distinct(Sol, Gridsize),																				%Colocar todas as linhas/colunas com elementos diferentes
				put_restrictions(Sol, Gridsize, SumT, SumR, SumB, SumL),													%Colocar restricoes de acordo com as listas
				append(Sol, Sol2),!,
				statistics(runtime, [T0| _]),    																			%Instante em que inicia o predicado labeling
				labeling([], Sol2),																							%Pesq da Solucao
				statistics(runtime, [T1|_]),    																			%instante em que termina o predicado labeling
				T is T1 - T0,
				format('Searching duration ~3d sec.~n', [T]),																%Print de estatisticas
				nl,draw_grid(Sol, Gridsize),nl,nl,nl.																		%Print da Solucao


%% choose(List, Elt) - chooses a random element
%% in List and unifies it with Elt.
choose([], []).
choose(List, Elt) :-
        length(List, Length),
        random(0, Length, Index),
        nth0(Index, List, Elt).

%% shuffle(ListIn, ListOut) - randomly shuffles
%% ListIn and unifies it with ListOut
shuffle([], []).
shuffle(List, [Element|Rest]) :-
        choose(List, Element),
        delete(List, Element, NewList),
        shuffle(NewList, Rest).

%Funcao para misturar cada linha/coluna da matriz
shuffle_grid(Sol, Shuffled):- shuffle(Sol, A), transpose(A, B), shuffle(B, Shuffled).

%Gridsize e' o tamanho desejado para a matriz aleatoria
easyAsSum(Gridsize):-

				length(SumT, Gridsize),length(SumR, Gridsize),length(SumB, Gridsize),length(SumL, Gridsize),		%Confirmar que ha o mesmo numero de elementos nas listas de restricao

				nl,nl,write('------E A S Y   A S   S U M------'),
				nl,nl,write('Grid: '),write(Gridsize),write('x'),write(Gridsize),nl,nl,

				( (Gridsize >= 5);
					write('Size must be > 4'),nl,nl,nl,fail
					),

				statistics(runtime, [T0| _]),    																			%Instante em que inicia o predicado labeling
				length(Sol, Gridsize),																						%Lista com o tamanho da grelha final
				len_row(Sol, Gridsize),				
				put_domains(Sol, Gridsize),																					%Colocar dominios
				put_distinct(Sol, Gridsize),																				%Colocar todas as linhas/colunas com elementos diferentes
				put_restrictions(Sol, Gridsize, SumT, SumR, SumB, SumL),													%Colocar restricoes de acordo com as listas
				append(Sol, Sol2),!,
		
				labeling([], Sol2),																							%Pesq da Solucao

				MaxSum is (Gridsize-1) + (Gridsize-2),																		%A soma maxima sera' a soma dos 2 maiores elementos do dominio
				domain(SumT, 1, MaxSum),
				labeling([], SumT),
				domain(SumR, 1, MaxSum),
				labeling([], SumR),
				domain(SumB, 1, MaxSum),
				labeling([], SumB),
				domain(SumL, 1, MaxSum),
				labeling([], SumL),

				shuffle_grid(Sol, Shufl), 
				length(ShuflST, Gridsize),length(ShuflSR, Gridsize),length(ShuflSB, Gridsize),length(ShuflSL, Gridsize),	%Cria aleatoriedade entre as linhas e colunas da matriz

				put_restrictions(Shufl, Gridsize, ShuflST, ShuflSR, ShuflSB, ShuflSL),										%Colocar restricoes de acordo com as listas
				append(Shufl, Shufl2),!,
				labeling([], Shufl2),!,
				domain(ShuflST, 1, MaxSum),
				labeling([], ShuflST),!,
				domain(ShuflSR, 1, MaxSum),
				labeling([], ShuflSR),!,
				domain(ShuflSB, 1, MaxSum),
				labeling([], ShuflSB),!,
				domain(ShuflSL, 1, MaxSum),
				labeling([], ShuflSL),!,    																			
				statistics(runtime, [T1|_]),    																			%instante em que termina o predicado labeling

				T is T1 - T0,
				nl,draw_grid(Shufl, Gridsize),nl,nl,nl,

				write('Top Constraints'),write(ShuflST),nl,
				write('Right Constraints'),write(ShuflSR),nl,
				write('Bottom Constraints'),write(ShuflSB),nl,
				write('Left Constraints'),write(ShuflSL),nl,

				format('Searching duration ~3d sec.~n', [T]),nl,nl.																%Print de estatisticas														