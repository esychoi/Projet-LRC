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


acquisition_prop_type2(Abi,Abil,Tbox) :-
  nl, write('Entrez la proposition a montrer (usage : `(concept1,concept2)`) :'), nl,
  read(P), /*format : (C1,C2) où C1 et C2 sont des concepts. */
  correction2(P),  /*verification syntaxique et semantique*/
  traitement2(P,Ptraite), /*P=(C1,C2), Ptraite = P où on a remplacé les concepts complexes par leur définition*/
  ajout2(Ptraite,Abi,Abil). /*ajout dans Abil*/

correction2((C1,C2)) :- concept(C1),concept(C2).
traitement2((C1,C2),(C1traite,C2traite)) :- remplace_concepts_complexes(C1,C1traite),
                                            remplace_concepts_complexes(C2,C2traite).
ajout2((C1traite,C2traite),Abi,Abil) :- genere(Nom),
                                        concatene([(Nom,and(C1traite,C2traite))],Abi,Abil).


/* PARTIE 3 : DEMONSTRATION DE LA PROPOSITION */

troisieme_etape(Abi,Abr) :- tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls),
                            resolution(Lie,Lpt,Li,Lu,Ls,Abr),
                            nl, write('Youpiiiiii, on a demontre la proposition initiale !!!').

tri_Abox([],Lie,Lpt,Li,Lu,Ls). /*cas d'arrêt*/
tri_Abox([(I,some(R,C))|T],Lie,Lpt,Li,Lu,Ls) :- concatene([(I,some(R,C))],Lie,LieNew), tri_Abox(T,LieNew,Lpt,Li,Lu,Ls). /*some -> Lie*/
tri_Abox([(I,all(R,C))|T],Lie,Lpt,Li,Lu,Ls) :- concatene([(I,all(R,C))],Lpt,LptNew), tri_Abox(T,Lie,LptNew,Li,Lu,Ls). /*all -> Lpt*/
tri_Abox([(I,and(C1,C2))|T],Lie,Lpt,Li,Lu,Ls) :- concatene([(I,and(C1,C2))],Li,LiNew), tri_Abox(T,Lie,Lpt,LiNew,Lu,Ls). /*and -> Li*/
tri_Abox([(I,or(C1,C2))|T],Lie,Lpt,Li,Lu,Ls) :- concatene([(I,or(C1,C2))],Lu,LuNew), tri_Abox(T,Lie,Lpt,Li,LuNew,Ls). /*or -> Lu*/
tri_Abox([(I,C)|T],Lie,Lpt,Li,Lu,Ls) :- concatene([(I,C)],Ls,LsNew), tri_Abox(T,Lie,Lpt,Li,Lu,LsNew). /*concept -> Ls*/
tri_Abox([(I,not(C))|T],Lie,Lpt,Li,Lu,Ls) :- concatene([(I,not(C))],Ls,LsNew), tri_Abox(T,Lie,Lpt,Li,Lu,LsNew). /*not(concept) -> Ls*/


resolution(Lie,Lpt,Li,Lu,Ls,Abr) :- complete_some(Lie,Lpt,Li,Lu,Ls,Abr). /*règle il existe*/
resolution(Lie,Lpt,Li,Lu,Ls,Abr) :- transformation_and(Lie,Lpt,Li,Lu,Ls,Abr). /*règle et*/
resolution(Lie,Lpt,Li,Lu,Ls,Abr) :- deduction_all(Lie,Lpt,Li,Lu,Ls,Abr). /*règle pour tout*/
resolution(Lie,Lpt,Li,Lu,Ls,Abr) :- transformation_or(Lie,Lpt,Li,Lu,Ls,Abr). /*règle ou*/


complete_some([(I,some(R,C))|Tie],Lpt,Li,Lu,Ls,Abr) :- genere(B), /*on cree un nouvel objet B*/
                                                       concatene([(I,B,R)],Abr,AbrNew), /*on ajoute (I,B,R) dans Abr*/
                                                       ajout3((B,C),Tie,Lpt,Li,Lu,Ls,Lie1,Lpt1,Li1,Lu1,Ls1), /*l'ajout de (B,C) depend de la nature de C*/
                                                       test_clash(Lie1,Lpt1,Li1,Lu1,Ls1,AbrNew), /*on regarde s'il y a un clash*/
                                                       resolution(Lie1,Lpt1,Li1,Lu1,Ls1,AbrNew). /*s'il n'y a pas de clash, on boucle*/

transformation_and(Lie,Lpt,[(I,and(C1,C2))|Ti],Lu,Ls,Abr) :- ajout3((I,C1),Lie,Lpt,Ti,Lu,Ls,Lie1,Lpt1,Li1,Lu1,Ls1),
                                                             ajout3((I,C2),Lie,Lpt,Ti,Lu,Ls,Lie1,Lpt1,Li1,Lu1,Ls1),
                                                             test_clash(Lie1,Lpt1,Li1,Lu1,Ls1,Abr),
                                                             resolution(Lie1,Lpt1,Li1,Lu1,Ls1,Abr).

deduction_all(Lie,Lpt,Li,Lu,Ls,Abr) :- presence_all(Lpt,Abr,(I,all(R,C)),(I,B,R)), /*on teste la presence d'un (I,all(R,C)) dans Lpt et d'un (I,B,R) dans Abr*/
                                       ajout3((B,C),Lie,Lpt,Li,Lu,Ls,Lie1,Lpt1,Li1,Lu1,Ls1),
                                       test_clash(Lie1,Lpt1,Li1,Lu1,Ls1,Abr),
                                       resolution(Lie1,Lpt1,Li1,Lu1,Ls1,Abr).

transformation_or(Lie,Lpt,Li,[(I,or(C1,C2))|Tu],Ls,Abr) :- ajout3((I,C1),Lie,Lpt,Li,Lu,Ls,Lie1g,Lpt1g,Li1g,Lu1g,Ls1g), /*ajout fils gauche*/
                                                           ajout3((I,C2),Lie,Lpt,Li,Lu,Ls,Lie1d,Lpt1d,Li1d,Lu1d,Ls1d), /*ajout fils droit*/
                                                           resolution(Lie1g,Lpt1g,Li1g,Lu1g,Ls1g,Abr), /*fils gauche*/
                                                           resolution(Lie1d,Lpt1d,Li1d,Lu1d,Ls1d,Abr). /*fils droit*/
