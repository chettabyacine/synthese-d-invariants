open Printf

(* Définitions de terme, test et programme *)
type term = 
  | Const of int
  | Var of int
  | Add of term * term
  | Mult of term * term

type test = 
  | Equals of term * term
  | LessThan of term * term

let tt = Equals (Const 0, Const 0)
let ff = LessThan (Const 0, Const 0)
 
type program = {nvars : int; 
                inits : term list; 
                mods : term list; 
                loopcond : test; 
                assertion : test}

let x n = "x" ^ string_of_int n

(* Question 1. Écrire des fonctions `str_of_term : term -> string` 
   et `str_of_test : test -> string` qui convertissent des termes 
   et des tests en chaînes de caractères du format SMTLIB.

  Par exemple, str_of_term (Var 3) retourne "x3", str_of_term (Add
   (Var 1, Const 3)) retourne "(+ x1 3)" et str_of_test (Equals (Var
   2, Const 2)) retourne "(= x2 2)".  *)
   
let rec str_of_term t =  match t with
  |Const(valeur) -> string_of_int valeur (*cas de base*)
  |Var(valeur) ->  x valeur (*cas de base avec la fonction x*)
  |Add(term1, term2) -> "(+ "^(str_of_term term1)^" "^(str_of_term term2)^")" (*cas récursif 1*)
  |Mult(term1, term2) -> "( * "^(str_of_term term1)^" "^(str_of_term term2)^")";; (*cas récursif 2*)

let str_of_test t = match t with
  |Equals(term1, term2) -> "(= "^(str_of_term term1)^" "^(str_of_term term2)^")" (* cas récursif 1*)
  |LessThan(term1, term2) -> "(< "^(str_of_term term1)^" "^(str_of_term term2)^")" (*cas récursif 2*)

let string_repeat s n =
  Array.fold_left (^) "" (Array.make n s)

(* Question 2. Écrire une fonction `str_condition : term list -> string`
   qui prend une liste de termes t1, ..., tk et retourne une chaîne 
   de caractères qui exprime que le tuple (t1, ..., tk) est dans 
   l'invariant.  Par exemple, str_condition [Var 1; Const 10] retourne 
   "(Inv x1 10)".
*)
let str_condition l = 
  (* la fonction contructeur retourne: x1 x2    xk) qui est concat avec (Invar *)
  let rec constructeur terms resultat = match terms with
    |[]-> resultat^")" (*cas de base: la liste est vide*)
    |t::autres_terms -> constructeur (autres_terms) (resultat^" "^(str_of_term t))  (*cas récursif: laisser des espaces entre chaque term *)
  in constructeur l ("(Invar");;

(* Question 3. Écrire une fonction 
   `str_assert_for_all : int -> string -> string` qui prend en
   argument un entier n et une chaîne de caractères s, et retourne
   l'expression SMTLIB qui correspond à la formule "forall x1 ... xk
   (s)".
     constructeur [t1, t2...tK] "Inv" 

  Par exemple, str_assert_forall 2 "< x1 x2" retourne : "(assert
   (forall ((x1 Int) (x2 Int)) (< x1 x2)))". 
   n=5, i=1 --> 1 *)

let str_assert s = "(assert " ^ s ^ ")"



let str_assert_forall n s = 
  (* entourer vars et cond par le mot clé: forall*)
  let str_forall vars cond = "(forall ("^vars^") ("^cond^"))" in

  (*générer un bloc forall avec toutes les variables entre x1 jusqu'à xnb puis rajouter à la fin la chaine s*)
  let rec constructeur_of_vars nb resultat = match nb with
    |1-> resultat^(x (n))^" Int)"
    |i-> constructeur_of_vars (i-1) (resultat^(x ((n- i)+1))^" Int) (")
  in 
  if (n<1) then str_assert ("("^s^")") (* si la condition necéssite aucune variable universelle*)
  else str_assert (str_forall (constructeur_of_vars n "(") s);; (* cas général. imbriqué forall dans une assert*)

(* Question 4. Nous donnons ci-dessous une définition possible de la
   fonction smt_lib_of_wa. Complétez-la en écrivant les définitions de
   loop_condition et assertion_condition. *)
  
   let generate_vars n =
    (* generate_vars 4 retourne [Var(1),Var(2),Var(3),Var(4)]*)
    let rec constructeur k res = match k with (*k est donc consommé jusqu'à zero*)
      |0-> res (* cas de la fin*)
      |i-> constructeur (i-1) (Var(i)::res) (*ajout d'une nouvelle variable*)
    in constructeur n [] ;;


let loop_condition_implication p = (* renvoie l'implication dans le bloc forall.*)
 (*gauche: (and (Invar(x1    xk)) (p.loopcond) *)
  let implication_gauche = "(and "^(str_condition (generate_vars p.nvars))^" "^(str_of_test p.loopcond)^")"
  in let implication_droite = str_condition p.mods (* droite Invar (p.mods) *)
  in "=> "^implication_gauche^" "^implication_droite;;


 let assertion_condition_implication p = 
(*gauche: (and (Invar x1    xk) (not(p.loopcond)))*)
  let implication_gauche = "(and "^(str_condition (generate_vars p.nvars))^" (not"^(str_of_test p.loopcond)^"))"
  in let implication_droite = str_of_test p.assertion (*droite: Invar(p.assertion)*)
  in "=> "^implication_gauche^" "^implication_droite;;;;


let smtlib_of_wa p = 
  let declare_invariant n =   "; synthèse d'invariant de programme\n"
  ^"; on déclare le symbole non interprété de relation Invar\n"
  ^"(declare-fun Invar (" ^ string_repeat "Int " n ^  ") Bool)" in

  let loop_condition p = "; la relation Invar est un invariant de boucle\n"
  ^(str_assert_forall p.nvars (loop_condition_implication p)) in 

  let initial_condition p = "; la relation Invar est vraie initialement\n"
  ^str_assert (str_condition p.inits) in

  let assertion_condition p =  "; l'assertion finale est vérifiée\n"
  ^(str_assert_forall p.nvars (assertion_condition_implication p)) in

  let call_solver =
    "; appel au solveur\n(check-sat-using (then qe smt))\n(get-model)\n(exit)\n" in
  String.concat "\n" [declare_invariant p.nvars;
                      loop_condition p;
                      initial_condition p;
                      assertion_condition p;
                      call_solver]

let p1 = {nvars = 2;
          inits = [(Const 0) ; (Const 0)];
          mods = [Add ((Var 1), (Const 1)); Add ((Var 2), (Const 3))];
          loopcond = LessThan ((Var 1),(Const 3));
          assertion = Equals ((Var 2),(Const 9))}

let () = Printf.printf "p1\n\n%s" (smtlib_of_wa p1);;



(* Question 5. Vérifiez que votre implémentation donne un fichier
   SMTLIB qui est équivalent au fichier que vous avez écrit à la main
   dans l'exercice 1. Ajoutez dans la variable p2 ci-dessous au moins
   un autre programme test, et vérifiez qu'il donne un fichier SMTLIB
   de la forme attendue. *)
 
(* p2 correspdant au programme java suivant:
    int i = 0;
		int v = 4;
		while (i < 20) {
			i = i + 1;
		  v = v + 5; 
		}
		assert (v==104);
    *)

let p2 = {nvars = 2;
   inits = [(Const 0) ; (Const 4)];
   mods = [Add ((Var 1), (Const 1)); Add ((Var 2), (Const 5))];
   loopcond = LessThan ((Var 1),(Const 6));
   assertion = Equals ((Var 2),(Const 34))}

   (* p3 correspdant au programme java suivant:
       
	    int x1 = 0;
		int x2 = 4;
		int x3= 3;
		while (x2 < 6) {
			x2 = x2 + 1;
		    x3 = x3 * 2;
		}
		assert (x1==0);
    *)

   let p3 = {
    nvars = 3;
  inits = [(Const 0); (Const 4); (Const 3)];
  mods = [(Var 1); Add((Var 2), Const 1); Mult((Var 3), Const 2)];
  loopcond = LessThan((Var 2), Const 6);
  assertion = Equals((Var 1),(Const 0))
   }

let () = Printf.printf "\n\np2\n\n%s" (smtlib_of_wa p2);;

let () = Printf.printf "\n\np3\n\n%s" (smtlib_of_wa p3);;


