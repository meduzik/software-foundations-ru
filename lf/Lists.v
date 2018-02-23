(** * Списки: работа со структурированными данными *)

Require Export Induction.
Module NatList.

(* ################################################################# *)
(** * Пары чисел *)

(** Когда мы определяем тип, используя команду [Inductive], каждый 
    конструктор может принимать любое число аргументов -- ни одного
    (как [true] или [O]), один (как [S]), или больше, например: *)

Inductive natprod : Type :=
| pair : nat -> nat -> natprod.

(** Это определение можно прочесть следующим образом: "существует
    только один способ задать пару чисел: применить конструктор [pair]
    к двум аргументам типа [nat]." *)

Check (pair 3 5).

(** Вот две простых функции для извлечения первого и второго компонента
    пары. Определения иллюстрируют, как выполнять соспоставление с
    образцом для конструкторов с несколькими аргументами. *)

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.

Compute (fst (pair 3 5)).
(* ===> 3 *)

(** Так как пары используются довольно часто, будет неплохо записывать
    их в стандартной математической нотации [(x,y)], а не [pair x y].
    Мы можем достичь этого командой [Notation]. *)

Notation "( x , y )" := (pair x y).

(** Эту новую нотацию для пар можно использовать и в выражениях, и
    при сопоставлении с образцом (разумеется, мы уже видели это в
    главе [Основы], при опредлении функции [minus] -- это работает,
    потому что нотация для пар включена в стандартную библиотеку): *)

Compute (fst (3,5)).

Definition fst' (p : natprod) : nat :=
  match p with
  | (x,y) => x
  end.

Definition snd' (p : natprod) : nat :=
  match p with
  | (x,y) => y
  end.

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

(** Давайте попробуем доказать несколько простых фактов о парах.

    Если мы сформулируем теорему в определенном (необычном) виде,
    мы можем завершить доказательство командой [reflexivity] (и ее
    способностями к упрощению): *)

Theorem surjective_pairing' : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof.
  reflexivity.  Qed.

(** Но [reflexivity] не поможет, если лемма сформулированна более
    естественным образом: *)

Theorem surjective_pairing_stuck : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  simpl. (* Ничего не делает! *)
Abort.

(** Нам нужно раскрыть структуру [p], чтобы тактика [simpl] могла
    выполнить сопоставление с образцом в [fst] и [snd]. Мы можем сделать
    это с помощью [destruct]. *)

Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p.  destruct p as [n m].  simpl.  reflexivity.  Qed.

(** Заметьте, что в отличие от случая с натуральными числами,
    [destruct] порождает только одну подцель. Это происходит из-за 
    того, что объект [natprod] может быть задан единственным образом. *)

(** **** Упражнение: 1 звезда (snd_fst_is_swap)  *)
Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  (* ЗАПОЛНИТЕ *) Admitted.
(** [] *)

(** **** Упражнение: 1 звезда, опциональное (fst_swap_is_snd)  *)
Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  (* ЗАПОЛНИТЕ *) Admitted.
(** [] *)

(* ################################################################# *)
(** * Списки чисел *)

(** Обобщая определние пар мы можем описать тип _списков_ чисел
    следующим образом: "Список либо пуст, либо это пара из числа и
    другого списка" *)

Inductive natlist : Type :=
  | nil  : natlist
  | cons : nat -> natlist -> natlist.

(** Например, список из трех элементов: *)

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

(** Как и с парами, удобнее будет использовать знакомую по другим
    языкам программирования нотацию для списков. Следующие определения
    позволяют использовать [::] как инфиксный оператор вместо [cons],
    и квадратные скобки как "внешний" оператор для списков. *)

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(** Не обязательно понимать все подробности этих определений, но если
    вы заинтересованы, вот что происходит. Аннотация [right 
    associativity] сообщает Coq, как следует читать выражения,
    включающие несколько применений оператора [::], так что, например,
    следующие записи означают одно и то же: *)

Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].

(** Часть [at level 60] говорит Coq, как читать выражения, включающие
    [::] и другие инфиксные операторы. Например, так как мы определили
    [+] в качестве инфиксной нотации для [plus] с уровнем 50:

    Notation "x + y" := (plus x y)
                      (at level 50, left associativity).

    оператор [+] имеет более высокий приоритет, чем [::], так что 
    выражение [1 + 2 :: [3]] будет прочитано как [(1 + 2) :: [3]],
    а не [1 + (2 :: [3])].

    (Выражения, подобные "[1 + 2 :: [3]]" могут сбивать с толку когда
    вы читаете их в файле .v. Внутрение скобки вокруг 3 обозначают
    список, в то время как внешние скобки, которые не видно в HTML,
    служат инструкцией для "coqdoc", что их содержимое следует 
    отображать как Coq, а не обычный текст.)

    Вторая и третья команды [Notation] определяют стандартную запись
    для списков с использованием квадратных скобок. Правая часть
    третьей нотации иллюстрирует синтаксис Coq для n-арной нотации
    и преобразования ее во вложенную последовательность бинарных
    конструкторов. *)

(* ----------------------------------------------------------------- *)
(** *** Повтор *)

(** Множество функций полезны при работе со списками. Например, функция
    [repeat] (повторить) принимает число [n] и число [count], и 
    возвращает список длиной [count], в котором каждый элемент равен
    [n]. *)

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

(* ----------------------------------------------------------------- *)
(** *** Длина *)

(** Функция [length] (длина) подсчитывает длину списка. *)

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

(* ----------------------------------------------------------------- *)
(** *** Конкатенация *)

(** Функция [app] (конкатенация) соединяет два списка. *)

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil    => l2
  | h :: t => h :: (app t l2)
  end.

(** На самом деле, функция [app] будет использоваться много раз в
    следующих частях, так что будет полезным задать для нее инфиксный
    оператор. *)

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Example test_app1:             [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity.  Qed.
Example test_app2:             nil ++ [4;5] = [4;5].
Proof. reflexivity.  Qed.
Example test_app3:             [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity.  Qed.

(* ----------------------------------------------------------------- *)
(** *** Голова (со значением по умолчанию) и хвост *)

(** Вот два небольших примера программирования на списках.
    Функция [hd] возвращает первый элемент ("голову") списка, а [tl]
    возвращает все, кроме первого элемента ("хвост"). Конечно же,
    пустой список не имеет первого элемента, так что мы должны
    передать значение по умолчанию, которое следует вернуть в этом
    случае. *)

Definition hd (default:nat) (l:natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tl (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

Example test_hd1:             hd 0 [1;2;3] = 1.
Proof. reflexivity.  Qed.
Example test_hd2:             hd 0 [] = 0.
Proof. reflexivity.  Qed.
Example test_tl:              tl [1;2;3] = [2;3].
Proof. reflexivity.  Qed.


(* ----------------------------------------------------------------- *)
(** *** Упражнения *)

(** **** Упражнение: 2 звезды, рекомендуется (list_funs)  *)
(** Заполните определения функций [nonzeros] (не нули), [oddmembers]
    (нечетные члены) и [countoddmemeber] (посчитать нечетные члены) 
    ниже. Взгляните на тесты, чтобы понять, что эти функции должны 
    делать. *)

Fixpoint nonzeros (l:natlist) : natlist
  (* ЗАМЕНИТЕ ЭТУ СТРОКУ НА ":= _ваше определение_ ." *). Admitted.

Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
  (* ЗАПОЛНИТЕ *) Admitted.
(* GRADE_THEOREM 0.5: NatList.test_nonzeros *)

Fixpoint oddmembers (l:natlist) : natlist
  (* ЗАМЕНИТЕ ЭТУ СТРОКУ НА ":= _ваше определение_ ." *). Admitted.

Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
  (* ЗАПОЛНИТЕ *) Admitted.
(* GRADE_THEOREM 0.5: NatList.test_oddmembers *)

Definition countoddmembers (l:natlist) : nat
  (* ЗАМЕНИТЕ ЭТУ СТРОКУ НА ":= _ваше определение_ ." *). Admitted.

Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
  (* ЗАПОЛНИТЕ *) Admitted.

Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
  (* ЗАПОЛНИТЕ *) Admitted.

Example test_countoddmembers3:
  countoddmembers nil = 0.
  (* ЗАПОЛНИТЕ *) Admitted.
(** [] *)

(** **** Упражнение: 3 звезды, продвинутое (alternate)  *)
(** Заполните определение [alternate], которое перемежает два списка
    в один, по очереди беря элементы из первого и второго списка.
    Посмотрите на тесты ниже, чтобы получить конкретные примеры.

    Заметьте, что естественный и элегантный способ записи функции
    [alternative] не пройдет проверку Coq на "завершимость" всех
    функций. Если вы обнаружите себя в этой ситуации, попробуйте найти
    более подробное решение, которое рассматривает оба списка 
    одновременно. (Одно из возможных решений требует определить новый
    тип пар, однако это не единственный путь.) *)

Fixpoint alternate (l1 l2 : natlist) : natlist
  (* ЗАМЕНИТЕ ЭТУ СТРОКУ НА ":= _ваше определение_ ." *). Admitted.

Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
  (* ЗАПОЛНИТЕ *) Admitted.

Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
  (* ЗАПОЛНИТЕ *) Admitted.

Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
  (* ЗАПОЛНИТЕ *) Admitted.

Example test_alternate4:
  alternate [] [20;30] = [20;30].
  (* ЗАПОЛНИТЕ *) Admitted.
(** [] *)

(* ----------------------------------------------------------------- *)
(** *** Мультимножества как списки *)

(** Мультимножество ([bag]) похоже на множество, но каждый элемент
    в нем может появляться много раз. Одна из возможных реализаций --
    представить мультимножество чисел как список. *)

Definition bag := natlist.

(** **** Упражнение: 3 звезды, рекомендуется (bag_functions)  *)
(** Заполните следующие определения функций [count](количество),
    [sum](сумма), [add](добавить) и [member](член) для 
    мультимножеств. *)

Fixpoint count (v:nat) (s:bag) : nat
  (* ЗАМЕНИТЕ ЭТУ СТРОКУ НА ":= _ваше определение_ ." *). Admitted.

(** Все следующие доказательства могут быть завершены при помощи
    одной команды [reflexivity]. *)

Example test_count1:              count 1 [1;2;3;1;4;1] = 3.
 (* ЗАПОЛНИТЕ *) Admitted.
Example test_count2:              count 6 [1;2;3;1;4;1] = 0.
 (* ЗАПОЛНИТЕ *) Admitted.
(* GRADE_THEOREM 0.5: NatList.test_count2 *)

(** Сумма мультимножеств ([sum]) похожа на объединение множеств:
    [sum a b] содержит все элементы [a] и [b]. (Математики обычно
    определяют объединение мультимножеств немного иначе -- используя
    максимум вместо суммы -- и поэтому мы не называем нашу операцию
    объединением.) Для функции [sum] мы записали заголовок, который
    не дает явные имена аргументам. Более того, мы использовали 
    команду [Definition] вместо [Fixpoint], так что даже если бы у вас
    были имена аргументов, вы бы не могли обработать их рекурсивно.
    Смысл такого ограничения в том, чтобы подтолкнуть вас к идее
    о том, каким еще образом можно определить функцию [sum] --
    возможно, используя те функции, которые мы уже определили. *)

Definition sum : bag -> bag -> bag
  (* ЗАМЕНИТЕ ЭТУ СТРОКУ НА ":= _ваше определение_ ." *). Admitted.

Example test_sum1:              count 1 (sum [1;2;3] [1;4;1]) = 3.
 (* ЗАПОЛНИТЕ *) Admitted.
(* GRADE_THEOREM 0.5: NatList.test_sum1 *)

Definition add (v:nat) (s:bag) : bag
  (* ЗАМЕНИТЕ ЭТУ СТРОКУ НА ":= _ваше определение_ ." *). Admitted.

Example test_add1:                count 1 (add 1 [1;4;1]) = 3.
 (* ЗАПОЛНИТЕ *) Admitted.
Example test_add2:                count 5 (add 1 [1;4;1]) = 0.
 (* ЗАПОЛНИТЕ *) Admitted.
(* GRADE_THEOREM 0.5: NatList.test_add1 *)
(* GRADE_THEOREM 0.5: NatList.test_add2 *)

Definition member (v:nat) (s:bag) : bool
  (* ЗАМЕНИТЕ ЭТУ СТРОКУ НА ":= _ваше определение_ ." *). Admitted.

Example test_member1:             member 1 [1;4;1] = true.
 (* ЗАПОЛНИТЕ *) Admitted.
(* GRADE_THEOREM 0.5: NatList.test_member1 *)
(* GRADE_THEOREM 0.5: NatList.test_member2 *)

Example test_member2:             member 2 [1;4;1] = false.
(* ЗАПОЛНИТЕ *) Admitted.
(** [] *)

(** **** Упражнение: 3 звезды, опциональное (bag_more_functions)  *)
(** Еще несколько функций над мультимножествами, чтобы 
    попрактиковаться. *)

(** Когда к мультимножеству, в котором нет элемента, применена функция 
    [remove_one] (удалить_один), оно должно остаться без изменений. *)

Fixpoint remove_one (v:nat) (s:bag) : bag
  (* ЗАМЕНИТЕ ЭТУ СТРОКУ НА ":= _ваше определение_ ." *). Admitted.

Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
  (* ЗАПОЛНИТЕ *) Admitted.

Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
  (* ЗАПОЛНИТЕ *) Admitted.

Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
  (* ЗАПОЛНИТЕ *) Admitted.

Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
  (* ЗАПОЛНИТЕ *) Admitted.

Fixpoint remove_all (v:nat) (s:bag) : bag (* удалить_все *)
  (* ЗАМЕНИТЕ ЭТУ СТРОКУ НА ":= _ваше определение_ ." *). Admitted.

Example test_remove_all1:  count 5 (remove_all 5 [2;1;5;4;1]) = 0.
 (* ЗАПОЛНИТЕ *) Admitted.
Example test_remove_all2:  count 5 (remove_all 5 [2;1;4;1]) = 0.
 (* ЗАПОЛНИТЕ *) Admitted.
Example test_remove_all3:  count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
 (* ЗАПОЛНИТЕ *) Admitted.
Example test_remove_all4:  count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
 (* ЗАПОЛНИТЕ *) Admitted.

Fixpoint subset (s1:bag) (s2:bag) : bool (* подмножество *)
  (* ЗАМЕНИТЕ ЭТУ СТРОКУ НА ":= _ваше определение_ ." *). Admitted.

Example test_subset1:              subset [1;2] [2;1;4;1] = true.
 (* ЗАПОЛНИТЕ *) Admitted.
Example test_subset2:              subset [1;2;2] [2;1;4;1] = false.
 (* ЗАПОЛНИТЕ *) Admitted.
(** [] *)

(** **** Упражнение: 3 звезды, рекомендуется (bag_theorem)  *)
(** Запишите интересную теорему о мультимножествах [bag_theorem],
    включающую функции [count] и [add], и докажите ее. Заметьте, что
    так как вы не ограничены в этой задача, может оказаться, что вы
    получите верную теорему, для доказательства которой потребуются
    техники, которые вы еще не изучили. Не стесняйтесь просить помощи,
    если застрянете! *)

(*
Theorem bag_theorem : ...
Proof.
  ...
Qed.
*)

(** [] *)

(* ################################################################# *)
(** * Reasoning About Lists *)

(** As with numbers, simple facts about list-processing
    functions can sometimes be proved entirely by simplification.  For
    example, the simplification performed by [reflexivity] is enough
    for this theorem... *)

Theorem nil_app : forall l:natlist,
  [] ++ l = l.
Proof. reflexivity. Qed.

(** ... because the [[]] is substituted into the
    "scrutinee" (the expression whose value is being "scrutinized" by
    the match) in the definition of [app], allowing the match itself
    to be simplified. *)

(** Also, as with numbers, it is sometimes helpful to perform case
    analysis on the possible shapes (empty or non-empty) of an unknown
    list. *)

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons n l' *)
    reflexivity.  Qed.

(** Here, the [nil] case works because we've chosen to define
    [tl nil = nil]. Notice that the [as] annotation on the [destruct]
    tactic here introduces two names, [n] and [l'], corresponding to
    the fact that the [cons] constructor for lists takes two
    arguments (the head and tail of the list it is constructing). *)

(** Usually, though, interesting theorems about lists require
    induction for their proofs. *)

(* ----------------------------------------------------------------- *)
(** *** Micro-Sermon *)

(** Simply reading example proof scripts will not get you very far!
    It is important to work through the details of each one, using Coq
    and thinking about what each step achieves.  Otherwise it is more
    or less guaranteed that the exercises will make no sense when you
    get to them.  'Nuff said. *)

(* ================================================================= *)
(** ** Induction on Lists *)

(** Proofs by induction over datatypes like [natlist] are a
    little less familiar than standard natural number induction, but
    the idea is equally simple.  Each [Inductive] declaration defines
    a set of data values that can be built up using the declared
    constructors: a boolean can be either [true] or [false]; a number
    can be either [O] or [S] applied to another number; a list can be
    either [nil] or [cons] applied to a number and a list.

    Moreover, applications of the declared constructors to one another
    are the _only_ possible shapes that elements of an inductively
    defined set can have, and this fact directly gives rise to a way
    of reasoning about inductively defined sets: a number is either
    [O] or else it is [S] applied to some _smaller_ number; a list is
    either [nil] or else it is [cons] applied to some number and some
    _smaller_ list; etc. So, if we have in mind some proposition [P]
    that mentions a list [l] and we want to argue that [P] holds for
    _all_ lists, we can reason as follows:

      - First, show that [P] is true of [l] when [l] is [nil].

      - Then show that [P] is true of [l] when [l] is [cons n l'] for
        some number [n] and some smaller list [l'], assuming that [P]
        is true for [l'].

    Since larger lists can only be built up from smaller ones,
    eventually reaching [nil], these two arguments together establish
    the truth of [P] for all lists [l].  Here's a concrete example: *)

Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons n l1' *)
    simpl. rewrite -> IHl1'. reflexivity.  Qed.

(** Notice that, as when doing induction on natural numbers, the
    [as...] clause provided to the [induction] tactic gives a name to
    the induction hypothesis corresponding to the smaller list [l1']
    in the [cons] case. Once again, this Coq proof is not especially
    illuminating as a static written document -- it is easy to see
    what's going on if you are reading the proof in an interactive Coq
    session and you can see the current goal and context at each
    point, but this state is not visible in the written-down parts of
    the Coq proof.  So a natural-language proof -- one written for
    human readers -- will need to include more explicit signposts; in
    particular, it will help the reader stay oriented if we remind
    them exactly what the induction hypothesis is in the second
    case. *)

(** For comparison, here is an informal proof of the same theorem. *)

(** _Theorem_: For all lists [l1], [l2], and [l3],
   [(l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3)].

   _Proof_: By induction on [l1].

   - First, suppose [l1 = []].  We must show

       ([] ++ l2) ++ l3 = [] ++ (l2 ++ l3),

     which follows directly from the definition of [++].

   - Next, suppose [l1 = n::l1'], with

       (l1' ++ l2) ++ l3 = l1' ++ (l2 ++ l3)

     (the induction hypothesis). We must show

       ((n :: l1') ++ l2) ++ l3 = (n :: l1') ++ (l2 ++ l3).

     By the definition of [++], this follows from

       n :: ((l1' ++ l2) ++ l3) = n :: (l1' ++ (l2 ++ l3)),

     which is immediate from the induction hypothesis.  [] *)

(* ----------------------------------------------------------------- *)
(** *** Reversing a List *)

(** For a slightly more involved example of inductive proof over
    lists, suppose we use [app] to define a list-reversing function
    [rev]: *)

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil    => nil
  | h :: t => rev t ++ [h]
  end.

Example test_rev1:            rev [1;2;3] = [3;2;1].
Proof. reflexivity.  Qed.
Example test_rev2:            rev nil = nil.
Proof. reflexivity.  Qed.

(* ----------------------------------------------------------------- *)
(** *** Properties of [rev] *)

(** Now let's prove some theorems about our newly defined [rev].
    For something a bit more challenging than what we've seen, let's
    prove that reversing a list does not change its length.  Our first
    attempt gets stuck in the successor case... *)

Theorem rev_length_firsttry : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = [] *)
    reflexivity.
  - (* l = n :: l' *)
    (* This is the tricky case.  Let's begin as usual
       by simplifying. *)
    simpl.
    (* Now we seem to be stuck: the goal is an equality
       involving [++], but we don't have any useful equations
       in either the immediate context or in the global
       environment!  We can make a little progress by using
       the IH to rewrite the goal... *)
    rewrite <- IHl'.
    (* ... but now we can't go any further. *)
Abort.

(** So let's take the equation relating [++] and [length] that
    would have enabled us to make progress and prove it as a separate
    lemma. *)

Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  (* WORKED IN CLASS *)
  intros l1 l2. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons *)
    simpl. rewrite -> IHl1'. reflexivity.  Qed.

(** Note that, to make the lemma as general as possible, we
    quantify over _all_ [natlist]s, not just those that result from an
    application of [rev].  This should seem natural, because the truth
    of the goal clearly doesn't depend on the list having been
    reversed.  Moreover, it is easier to prove the more general
    property. *)

(** Now we can complete the original proof. *)

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons *)
    simpl. rewrite -> app_length, plus_comm.
    simpl. rewrite -> IHl'. reflexivity.  Qed.

(** For comparison, here are informal proofs of these two theorems:

    _Theorem_: For all lists [l1] and [l2],
       [length (l1 ++ l2) = length l1 + length l2].

    _Proof_: By induction on [l1].

    - First, suppose [l1 = []].  We must show

        length ([] ++ l2) = length [] + length l2,

      which follows directly from the definitions of
      [length] and [++].

    - Next, suppose [l1 = n::l1'], with

        length (l1' ++ l2) = length l1' + length l2.

      We must show

        length ((n::l1') ++ l2) = length (n::l1') + length l2).

      This follows directly from the definitions of [length] and [++]
      together with the induction hypothesis. [] *)

(** _Theorem_: For all lists [l], [length (rev l) = length l].

    _Proof_: By induction on [l].

      - First, suppose [l = []].  We must show

          length (rev []) = length [],

        which follows directly from the definitions of [length]
        and [rev].

      - Next, suppose [l = n::l'], with

          length (rev l') = length l'.

        We must show

          length (rev (n :: l')) = length (n :: l').

        By the definition of [rev], this follows from

          length ((rev l') ++ [n]) = S (length l')

        which, by the previous lemma, is the same as

          length (rev l') + length [n] = S (length l').

        This follows directly from the induction hypothesis and the
        definition of [length]. [] *)

(** The style of these proofs is rather longwinded and pedantic.
    After the first few, we might find it easier to follow proofs that
    give fewer details (which can easily work out in our own minds or
    on scratch paper if necessary) and just highlight the non-obvious
    steps.  In this more compressed style, the above proof might look
    like this: *)

(** _Theorem_:
     For all lists [l], [length (rev l) = length l].

    _Proof_: First, observe that [length (l ++ [n]) = S (length l)]
     for any [l] (this follows by a straightforward induction on [l]).
     The main property again follows by induction on [l], using the
     observation together with the induction hypothesis in the case
     where [l = n'::l']. [] *)

(** Which style is preferable in a given situation depends on
    the sophistication of the expected audience and how similar the
    proof at hand is to ones that the audience will already be
    familiar with.  The more pedantic style is a good default for our
    present purposes. *)



(* ================================================================= *)
(** ** [Search] *)

(** We've seen that proofs can make use of other theorems we've
    already proved, e.g., using [rewrite].  But in order to refer to a
    theorem, we need to know its name!  Indeed, it is often hard even
    to remember what theorems have been proven, much less what they
    are called.

    Coq's [Search] command is quite helpful with this.  Typing
    [Search foo] will cause Coq to display a list of all theorems
    involving [foo].  For example, try uncommenting the following line
    to see a list of theorems that we have proved about [rev]: *)

(*  Search rev. *)

(** Keep [Search] in mind as you do the following exercises and
    throughout the rest of the book; it can save you a lot of time!

    If you are using ProofGeneral, you can run [Search] with [C-c
    C-a C-a]. Pasting its response into your buffer can be
    accomplished with [C-c C-;]. *)

(* ================================================================= *)
(** ** List Exercises, Part 1 *)

(** **** Упражнение: 3 звезды (list_exercises)  *)
(** More practice with lists: *)

Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
  (* ЗАПОЛНИТЕ *) Admitted.
(* GRADE_THEOREM 0.5: NatList.app_nil_r *)

Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  (* ЗАПОЛНИТЕ *) Admitted.
(* GRADE_THEOREM 0.5: NatList.rev_app_distr *)

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  (* ЗАПОЛНИТЕ *) Admitted.
(* GRADE_THEOREM 0.5: NatList.rev_involutive *)

(** There is a short solution to the next one.  If you find yourself
    getting tangled up, step back and try to look for a simpler
    way. *)

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  (* ЗАПОЛНИТЕ *) Admitted.
(* GRADE_THEOREM 0.5: NatList.app_assoc4 *)

(** An exercise about your implementation of [nonzeros]: *)

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  (* ЗАПОЛНИТЕ *) Admitted.
(** [] *)

(** **** Упражнение: 2 звезды (beq_natlist)  *)
(** Fill in the definition of [beq_natlist], which compares
    lists of numbers for equality.  Prove that [beq_natlist l l]
    yields [true] for every list [l]. *)

Fixpoint beq_natlist (l1 l2 : natlist) : bool
  (* ЗАМЕНИТЕ ЭТУ СТРОКУ НА ":= _ваше определение_ ." *). Admitted.

Example test_beq_natlist1 :
  (beq_natlist nil nil = true).
 (* ЗАПОЛНИТЕ *) Admitted.

Example test_beq_natlist2 :
  beq_natlist [1;2;3] [1;2;3] = true.
(* ЗАПОЛНИТЕ *) Admitted.

Example test_beq_natlist3 :
  beq_natlist [1;2;3] [1;2;4] = false.
 (* ЗАПОЛНИТЕ *) Admitted.

Theorem beq_natlist_refl : forall l:natlist,
  true = beq_natlist l l.
Proof.
  (* ЗАПОЛНИТЕ *) Admitted.
(** [] *)

(* ================================================================= *)
(** ** List Exercises, Part 2 *)

(** Here are a couple of little theorems to prove about your
    definitions about bags above. *)

(** **** Упражнение: 1 звезда (count_member_nonzero)  *)
Theorem count_member_nonzero : forall (s : bag),
  leb 1 (count 1 (1 :: s)) = true.
Proof.
  (* ЗАПОЛНИТЕ *) Admitted.
(** [] *)

(** The following lemma about [leb] might help you in the next exercise. *)

Theorem ble_n_Sn : forall n,
  leb n (S n) = true.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* 0 *)
    simpl.  reflexivity.
  - (* S n' *)
    simpl.  rewrite IHn'.  reflexivity.  Qed.

(** **** Упражнение: 3 звезды, продвинутое (remove_decreases_count)  *)
Theorem remove_decreases_count: forall (s : bag),
  leb (count 0 (remove_one 0 s)) (count 0 s) = true.
Proof.
  (* ЗАПОЛНИТЕ *) Admitted.
(** [] *)

(** **** Упражнение: 3 звезды, опциональное (bag_count_sum)  *)
(** Write down an interesting theorem [bag_count_sum] about bags
    involving the functions [count] and [sum], and prove it using
    Coq.  (You may find that the difficulty of the proof depends on
    how you defined [count]!) *)
(* ЗАПОЛНИТЕ *)
(** [] *)

(** **** Упражнение: 4 звезды, продвинутое (rev_injective)  *)
(** Prove that the [rev] function is injective -- that is,

    forall (l1 l2 : natlist), rev l1 = rev l2 -> l1 = l2.

(There is a hard way and an easy way to do this.) *)

(* ЗАПОЛНИТЕ *)
(** [] *)

(* ################################################################# *)
(** * Options *)

(** Suppose we want to write a function that returns the [n]th
    element of some list.  If we give it type [nat -> natlist -> nat],
    then we'll have to choose some number to return when the list is
    too short... *)

Fixpoint nth_bad (l:natlist) (n:nat) : nat :=
  match l with
  | nil => 42  (* arbitrary! *)
  | a :: l' => match beq_nat n O with
               | true => a
               | false => nth_bad l' (pred n)
               end
  end.

(** This solution is not so good: If [nth_bad] returns [42], we
    can't tell whether that value actually appears on the input
    without further processing. A better alternative is to change the
    return type of [nth_bad] to include an error value as a possible
    outcome. We call this type [natoption]. *)

Inductive natoption : Type :=
  | Some : nat -> natoption
  | None : natoption.

(** We can then change the above definition of [nth_bad] to
    return [None] when the list is too short and [Some a] when the
    list has enough members and [a] appears at position [n]. We call
    this new function [nth_error] to indicate that it may result in an
    error. *)

Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => match beq_nat n O with
               | true => Some a
               | false => nth_error l' (pred n)
               end
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [4;5;6;7] 3 = Some 7.
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [4;5;6;7] 9 = None.
Proof. reflexivity. Qed.

(** (In the HTML version, the boilerplate proofs of these
    examples are elided.  Click on a box if you want to see one.)

    This example is also an opportunity to introduce one more small
    feature of Coq's programming language: conditional
    expressions... *)


Fixpoint nth_error' (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => if beq_nat n O then Some a
               else nth_error' l' (pred n)
  end.

(** Coq's conditionals are exactly like those found in any other
    language, with one small generalization.  Since the boolean type
    is not built in, Coq actually supports conditional expressions over
    _any_ inductively defined type with exactly two constructors.  The
    guard is considered true if it evaluates to the first constructor
    in the [Inductive] definition and false if it evaluates to the
    second. *)

(** The function below pulls the [nat] out of a [natoption], returning
    a supplied default in the [None] case. *)

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.

(** **** Упражнение: 2 звезды (hd_error)  *)
(** Using the same idea, fix the [hd] function from earlier so we don't
    have to pass a default element for the [nil] case.  *)

Definition hd_error (l : natlist) : natoption
  (* ЗАМЕНИТЕ ЭТУ СТРОКУ НА ":= _ваше определение_ ." *). Admitted.

Example test_hd_error1 : hd_error [] = None.
 (* ЗАПОЛНИТЕ *) Admitted.

Example test_hd_error2 : hd_error [1] = Some 1.
 (* ЗАПОЛНИТЕ *) Admitted.

Example test_hd_error3 : hd_error [5;6] = Some 5.
 (* ЗАПОЛНИТЕ *) Admitted.
(** [] *)

(** **** Упражнение: 1 звезда, опциональное (option_elim_hd)  *)
(** This exercise relates your new [hd_error] to the old [hd]. *)

Theorem option_elim_hd : forall (l:natlist) (default:nat),
  hd default l = option_elim default (hd_error l).
Proof.
  (* ЗАПОЛНИТЕ *) Admitted.
(** [] *)

End NatList.

(* ################################################################# *)
(** * Partial Maps *)

(** As a final illustration of how data structures can be defined in
    Coq, here is a simple _partial map_ data type, analogous to the
    map or dictionary data structures found in most programming
    languages. *)

(** First, we define a new inductive datatype [id] to serve as the
    "keys" of our partial maps. *)

Inductive id : Type :=
  | Id : nat -> id.

(** Internally, an [id] is just a number.  Introducing a separate type
    by wrapping each nat with the tag [Id] makes definitions more
    readable and gives us the flexibility to change representations
    later if we wish. *)

(** We'll also need an equality test for [id]s: *)

Definition beq_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => beq_nat n1 n2
  end.

(** **** Упражнение: 1 звезда (beq_id_refl)  *)
Theorem beq_id_refl : forall x, true = beq_id x x.
Proof.
  (* ЗАПОЛНИТЕ *) Admitted.
(** [] *)

(** Now we define the type of partial maps: *)

Module PartialMap.
Export NatList.
  
Inductive partial_map : Type :=
  | empty  : partial_map
  | record : id -> nat -> partial_map -> partial_map.

(** This declaration can be read: "There are two ways to construct a
    [partial_map]: either using the constructor [empty] to represent an
    empty partial map, or by applying the constructor [record] to
    a key, a value, and an existing [partial_map] to construct a
    [partial_map] with an additional key-to-value mapping." *)

(** The [update] function overrides the entry for a given key in a
    partial map (or adds a new entry if the given key is not already
    present). *)

Definition update (d : partial_map)
                  (x : id) (value : nat)
                  : partial_map :=
  record x value d.

(** Last, the [find] function searches a [partial_map] for a given
    key.  It returns [None] if the key was not found and [Some val] if
    the key was associated with [val]. If the same key is mapped to
    multiple values, [find] will return the first one it
    encounters. *)

Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  | empty         => None
  | record y v d' => if beq_id x y
                     then Some v
                     else find x d'
  end.


(** **** Упражнение: 1 звезда (update_eq)  *)
Theorem update_eq :
  forall (d : partial_map) (x : id) (v: nat),
    find x (update d x v) = Some v.
Proof.
 (* ЗАПОЛНИТЕ *) Admitted.
(** [] *)

(** **** Упражнение: 1 звезда (update_neq)  *)
Theorem update_neq :
  forall (d : partial_map) (x y : id) (o: nat),
    beq_id x y = false -> find x (update d y o) = find x d.
Proof.
 (* ЗАПОЛНИТЕ *) Admitted.
(** [] *)
End PartialMap.

(** **** Упражнение: 2 звезды (baz_num_elts)  *)
(** Consider the following inductive definition: *)

Inductive baz : Type :=
  | Baz1 : baz -> baz
  | Baz2 : baz -> bool -> baz.

(** How _many_ elements does the type [baz] have?
    (Explain your answer in words, preferrably English.)

(* ЗАПОЛНИТЕ *)
*)
(** [] *)

(** $Date: 2017-11-16 01:44:48 -0500 (Thu, 16 Nov 2017) $ *)

