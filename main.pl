/* PROJET LRC - M1 DAC */
/* ESTHER CHOI - GROUPE 1 */

:- [utils].

compteur(1).

/* PARTIE 1 : PRELIMINAIRES */

:- [td4exo3].

/*TBox :
[(sculpteur,and(personne,some(aCree,sculpture))), (auteur,and(personne,some(aEcrit,livre))), (editeur,and(personne,and(not(some(aEcrit,livre)),some(aEdite,livre)))), (parent,and(personne,some(aEnfant,anything)))]
*/

/*ABox :
  - assertions de concepts :
[(michelAnge,personne), (david,sculpture), (sonnets,livre), (vinci,personne), (joconde,objet)]
  - assertions de rôles :
  [(michelAnge, david, aCree), (michelAnge, sonnet, aEcrit),(vinci, joconde, aCree)]
*/



programme :- premiere_etape(Tbox,Abi,Abr),
             deuxieme_etape(Abi,Abil,Tbox),
             troisieme_etape(Abil,Abr).

/*Paramètres
- premiere_etape :
  Tbox = liste représentant la TBox
  Abi = liste représentant les assertions de concepts de la ABox
  Abr = liste représentant les assertions de rôles de la ABox
- deuxieme_etape :
  Abi = liste des assertions de concepts initiales
  Abil = liste des assertions de concepts complétée après la soumission d'une proposition a demontrer
  Tbox = liste représentant la TBox
- troisieme_etape :
  Abil = liste des assertions de concepts complétée
  Abr =  liste des assertions de rôles qui peut également évoluer lors de la démonstration
*/

premiere_etape(
  [(sculpteur,and(personne,some(aCree,sculpture))), (auteur,and(personne,some(aEcrit,livre))), (editeur,and(personne,and(not(some(aEcrit,livre)),some(aEdite,livre)))), (parent,and(personne,some(aEnfant,anything)))],
  [(michelAnge,personne), (david,sculpture), (sonnets,livre), (vinci,personne), (joconde,objet)],
  [(michelAnge, david, aCree), (michelAnge, sonnet, aEcrit),(vinci, joconde, aCree)]
).


/* PARTIE 2 : SAISIE DE LA PROPOSITION A DEMONTRER */

deuxieme_etape(Abi,Abil,Tbox) :-
  saisie_et_traitement_prop_a_demontrer(Abi,Abil,Tbox).

saisie_et_traitement_prop_a_demontrer(Abi,Abil,Tbox) :-
  nl, write('Entrez le numero du type de proposition que vous voulez demontrer :'), nl,
  write('1 = Une instance donnee appartient a un concept donne.'), nl,
  write('2 = Deux concepts n"ont pas d"elements en commun (ils ont une intersection vide).'), nl,
  read(R), suite(R,Abi,Abil,Tbox).

suite(1,Abi,Abil,Tbox) :- acquisition_prop_type1(Abi,Abil,Tbox),!.
suite(2,Abi,Abil,Tbox) :- acquisition_prop_type2(Abi,Abil,Tbox),!.
suite(R,Abi,Abil,Tbox) :- nl, write('Cette reponse est incorrecte'),nl,
  saisie_et_traitement_prop_a_demontrer(Abi,Abil,Tbox).

acquisition_prop_type1(Abi,Abil,Tbox) :-
  nl, write('Entrez la proposition a montrer :'), nl,
  read(P), /*format : (I,C) où I est une instance et C un concept existants. */
  correction(P),  /*verification syntaxique et semantique*/
  traitement(P,Ptraitennf), /*P=(I,C), Ctraitennf = nnf de not(C)*/
  ajout(Ptraitennf,Abi,Abil). /*ajout dans Abil*/

correction((I,C)) :- iname(I),concept(C).
traitement((I,C),(I,Ctraitennf)) :- remplace_concepts_complexes(C,Ctraite),
                                    nnf(not(Ctraite),Ctraitennf).
ajout(Ptraitennf,Abi,Abil) :- concatene([Ptraitennf],Abi,Abil).


acquisition_prop_type2(Abi,Abil,Tbox) :- nl,nl,write('TODO1').


/* PARTIE 3 : DEMONSTRATION DE LA PROPOSITION */
troisieme_etape(Abi,Abr) :- nl,nl,nl, write('TODO2').

/*
troisieme_etape(Abi,Abr) :- tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls),
                            resolution(Lie,Lpt,Li,Lu,Ls,Abr),
                            nl, write('Youpiiiiii, on a demontre la proposition initiale !!!')

tri_Abox([(I,some(R,C))|T],Lie,Lpt,Li,Lu,Ls) :- tri_Abox(T,concatene(Lie,[(I,some(R,C))],Lie),Lpt,Li,Lu,Ls).
tri_Abox([(I,all(R,C))|T],Lie,Lpt,Li,Lu,Ls) :- tri_Abox(T,Lie,concatene(Lpt,[(I,all(R,C))],Lpt),Li,Lu,Ls).
tri_Abox([(I,and(C1,C2))|T],Lie,Lpt,Li,Lu,Ls) :- tri_Abox(T,Lie,Lpt,concatene(Li,[(I,and(C1,C2))],Li),Lu,Ls).
tri_Abox([(I,or(C1,C2))|T],Lie,Lpt,Li,Lu,Ls) :- tri_Abox(T,Lie,Lpt,Li,concatene(Lu,[(I,or(C1,C2))],Lu),Ls).
tri_Abox([(I,C)|T],Lie,Lpt,Li,Lu,Ls) :- tri_Abox(T,Lie,Lpt,Li,Lu,concatene(Ls,[(I,C)],Ls)).
tri_Abox([(I,not(C))|T],Lie,Lpt,Li,Lu,Ls) :- tri_Abox(T,Lie,Lpt,Li,Lu,concatene(Ls,[(I,not(C))],Ls)).

resolution([(A,B,some(R,C))|T],Lpt,Li,Lu,Abr) :- complete_some(Lie,Lpt,Li,Lu,concatene(Abr,[(A,B,R)],Abr)).
*/
