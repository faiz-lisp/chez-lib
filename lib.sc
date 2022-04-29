
(define (version) "chez-lib v2.00") ;
(define (git-url) "https://gitxx.com/faiz-xxxx/chez-lib.git")

#|
== Chez-lib.sc (mainly for Windows NT) - written by Faiz ==
   ________  __                            __   __  _
  /    ___ \|  |__   ____ _______         |  | |__|| |__
  /    \  \/|  |  \_/ __ \\__   /   _____ |  | |  || __ \
  \     \___|  |\  |  ___/  /  /_  /____/ |  |_|  || \_| \
   \_______/\__||__|\____/ /_____\        |____/__|\_____/

  - Update notes:
    - 2.00
      -  V add: same
      -  v upd: try exp [ret]
      -  U chg: range->myrange, since rkt has diffe range
      -  u upd: (in-range num s e [lt <=] [lt2 nil])
      -  T add: rand-elem xs
      -  t add: void*
      -  S upd: ty: str->sym, str/sep%
      -  s add: withs?
      -  R upd: pop
      -  r add: key->nth
      -  Q add: x=>y? x y xys [defa nil]
      -  q upd: memorized-fx
      -  P upd: remov .. [g nil]
      -  p add: num->nums/carry
      -  O add: (fmt-nums/carry '(23 23 123) '(24 60 60 1000))
      -  o add: (lam-unify '(lam (x y) (list x y))) -> '(lam (x1 x2) (list x1 x2))
      -  N add: (cap-upcase "asd") -> "Asd"
      -  M add: (list/merge xs ys [f-sel])
      -  m add: displn
      -  L upd: nx->list
      -  K chg: stru> ~> any>
      -  k fix: map-for-combinations
      -  J add: defs which is like setq for inner
      -  j add: rgb->yuv
      -  I Add: data-compress for pic
      -  H upd: collect supp in
      -  h add: sort-by-sames xs > > [append? T]
      -  G add: euler
      -  g add: y=fx y=fx->paras
      -  F add: mt/xxx for matrix
      -  e add: ~range x0 n [f]
      -  C add: rmap
      -  c add: (time->sec (get-time))
      -  A add: (key->kv kvs key [= eql])
      -  a add: (filter-nths (curry eq 5) '(1 123  5 654 6 5 2)) ;-> nths
    - 1.99
      - ZZ add: (map1/nths (lam (x) (list x)) '(1 2 213 123) '(2 4) F) ;-> '(1 [2] 213 [123])
      - Zz add: (.% 1.27 0.02) ;->0.01
      - Zy add: chg-val-by-key kvs k v [k= eql], chg-vals-by-keys kvs kvs-new [k=]
      - ZX upd: flow
      - Zx add: chg-nth% xs iths [value nil] [base 1]
      - Zw add: (id/f cadr 1 2 3) ;~> 2
      - Zv add: (setf! xs func car 3) ;
      - ZU add: sleep-sec 1.01, sleep-ms 1010
      - Zt add: get-time ~> '(9 0 0)
      - ZS upd: divide-before
      - Zs Add: rand-filename
      - ZR add: max-cnt-of-same: xs [lt <]
      - Zr add: get-https-ret: url [tmp-file]
      - ZQ upd: tail%
      - Zq chg: digest%
      - ZP add: int<->list/scale
      - Zp upd: list/nth xs [n0 1]
      - Zn upd: int->str/system
      - Zm add: -% cmp% close-to%
      - ZL add: str-count
      - Zl upd: .avg
      - ZK fas: myround -> round*
      - ZJ upd: ~=; add: pow/, pow-root
      - ZI fix: deep&
      - Zi add: int->list next-to
      - Zg add: fold% exist-same? max-min
      - Zf upd: randnums fold int
      - Ze upd: range/total api-ls
      - Zd add: rotate! walk
      - Zc fas: factors
      - Zb add: do-for-pairs, odds, demo/fac~
      - Za add: let/ad*
      - Z  add: head-tail%, mysort
      - z  add: file/cont, keys->vals, flip, fill-lhs/rhs, rgb<->565;\n Fix : groups, arb-group
      - Y  fix: files/cont: more?
      - y  Fix: choose: once?
      - W  add: rand-seq
      - v  add: ref%, ref*, refs*
      - T  add: chg-nth, chg-ref-val ;
      - S  upd: refs nths xths pts->vals
      - r  upd: demo maze
      - Q  upd: str-repl%, replace% can CRUD ;
      - O  add: (do-for xs conv deconv)
      - L  add: elem-freq, mem?-and-do
      - K  add: save-bin-file
      - I  add: strcat/sep-per flow load-binary-file
      - i  Upd: (save-file cont file [codec "utf-8"])
      - h  add: replaces, str-repls, get-file-var ...
      - G  upd: divide
      - F  add: str-trim-all
      - D  upd: case (compose); fix : gotcha;
      - -  add: int<->str/system, digit<->char, global vars
    - 1.98
      -  Z add: separa, strcat/sep
      -  X add: str-divides, file-ext, str/sep-chars
      -  W add: str-exist?
      -  S add: load-file
      -  r add: key->val xz x
      -  Q add: (divide-after '(x m k y m k z) '(m k)) ~> '([x m k] [y m k] [z]); divide; str-divide
      -  p Upd: (lisp nil) ~> F
      -  O add: path operations and grep
      -  o add: range/total
      -  n add: (fixnum 1/1.2);\n upd : (sleep 1.0);
      -  I add: make-file, make-path
      -  C add: (list/seps '(1 2 3) '(4 5)) ~> '(1 4 5 2 4 5 3)
      -  B Add: (lam/lams ([(a) b] c . xs) [append (list a b c) xs])
    - 1.97
      -  w Add: (deep& rev char-downcase '((#\a #\s) #\D)) ~> '(#\d (#\s #\a))
      -  v Add: (deep-exist-match? [lam (x) (cn-char? x)] '((#\我) #\3)) ~> T
      -  Q Add: (trim '(1 2 1 2 1 1 2 3 1 2) '(1 2)) ~> '(1 1 2 3) ;
      -  O upd: (beep [456] [500]);\nadd : getcwd;
      -  N add: def-ffi, shell-execute
      -  L fix: for: map -> for-each; upd : tail=list-tail; add : tail%
      -  c Add: htab-:kvs,keys,values
      -  - Add: (doc-ls co) -> documentable-keys -> '(cons cond); house keeping;
    - 1.96 Add: docs, def/doc, doc, doc-paras
    - 1.95 Upd: fold (_ f x xs), foldl-n (_ n fn xs), infix->prefix (_ xs), ./
    - 1.94 Add: self-act (_ pow 2 3) => (pow 2 2 2), rev-calc (_ pow 4) => 2
    - 1.93 Simp algo: fast-expt, (_ g x [n 1])

  - Suffixes:
    - @ slow / bad
    - % theoretic / internal / paras->list
    - %B big / cost more memory space
    - %win for Windows
    - ~ just faster
    - * multi-functional (or optimized)
    - ! (forced or) with side-effect

  - prefixes:
    - sy/ syt/ for syntax
    - ~ returns a reversed result

  - /: means with something or in a namespace

  - vars:
    - ~var: temp variety
    - *global-var*
    - %glob-tmp-var%

  - editions/parts:
    - idea; ideal; refined; stable;
    - fast; Grace; safe
    - std, core, ex, idea, main

  - Which ops are slow?: (sequence: fast->slow)
    ~ guard match
    - last-pair last list?
    - length
    - append->conz->rpush ... slowest
    - redu > foldl > eval > compose/curry? > evs > match?
    - strcat
    - remove
    - list->vec vec->list
  - fast>:
    - consp -> atomp, nilp, lisp, eq
    - sort, .., cond if, .., redu, map, .., append;
    - syntax, func
    - def_ set!~def alias
    - cons vector list
  - not the fastest achievement:
    - reverse append! list-copy
  - - apply let
    - eq =, eql

  - todo:
    - lam/va, lam-macro
    - pcre->match
    - (deep-action/apply g xs [seq]): d-remov
    - end->car
    - control[include convert]: strings, files, ...
    - ~(!= 1 2 1), (> 3 2 1), (coprime? 2 15 4)
    - (part-of-num 123456 -3 2)~> 45
    - see to: verb.adj.a./act, prep./judge,
    - lam_ lam/ret
    - [random-seed (floor->fix(w* (elapse(fib 500000))))] ;too closed ;~> parallel universe id bytes, not work well
      - time.ms->md5->cost.ns?
      - . time activities info net:salt io? file:psw/md5
    - (nthof-g-resl rand '(3 1 4) [max-n 10000000])
    - (nthof-g rand nth [len 1])
    - grep grep-rn
    - reload? load compile udp/tcp get/post v3 juce ui test trace
    - if(!#f/nil): cadr caddr cadddr eval, repl
    - cond case, for map lambda foldl reduce curry recursion repl foldr
    - ? (str/sep sep . xs)
      - -> echo
      - => any->int
    - (_ xs . x) (-> -> x)
    - trans-code: dsl->std
    - church yc algo
    - structure:
      - skip-list/max-skip-step/for-spec-type/with-logic, path
        - ?`[(4) ([(1 a) 2 3] [4 5 6])]
      - b+tree
    - AI
    - math memo combinations, eval. match
    - https usd/usdt pcre
    - def/setq-glob
    - car! (cons 1 2 '()) cons! conz!
    - rev!
    - seems that newlisp call scheme and c will be more free.
    - to optimize
    - to fix
      - don't overwrite chez api
        - assert cxxxxr command-line break collect collections delay div exp expand gcd xor odd?
      - save-file
      - replace

  - cant/hard: get-addr
  - cant implete:
    - apply call/cc?

  - seq of implements:
    - (g x y) -> apply -> curry

  - modules
    - syntax
      - define
      - setq
      - match
      - short-hand
    - list
    - string
    - API
      - type
      - disp
      - funcs
      - demo
    - file
    - C
    - struct
    - conv
    - math
    - algo
    - AI
    - module/topic
      - root
      - church
      - sicp
      - onlisp
      - prolog
      - yin
      - faiz
    - misc
    - setting
      - fn/short-hand
    - data
    - main
      - exp/idea
    - clean

  - tolearn:
    - match
    - import
    - fork-thread
    - profile
    - eg: chez/examples/matrix.ss
    - my: let + redu sort! rand eval
    - hygienic assq memq define-structure
    - >: [syntax-case see to ;push] defsyt def
    - ;define-syntax syntax-rules syntax->datum=datum
    - datum->syntax=syntax=#' with-syntax with-implicit syntax-case #, fluid-let-syntax ...
    - (let ([ret ..]) (ev `(setq x ',ret))
    - un/trace debug
    - list: -tail/head/ref
    - apis: #%$xxx
    - (trace funxxx) (funxxx ...) can show is it a tail form rec
    - hash when def/setq/defsyt ~> api-search
    - vec: cons lam/vec def/vec, map for redu, add! del/rm! flat strcat
    - sy: rev, vec? flat append? group
    - sort: qsort heap merge
    - abs(fxnum) <= 2^29-1 (> 5E)
    - (eval-when (compile) (optimize-level 3))
  - learned
    - collect ~= manual-gc
    - body... != body ...
    - let-values(<->)
    - def-syt doesnt supp recursion directly, but case
    - def-syt cant be in ano def-syn

  - beauties:
    - reverse flat deep-length bump

  - to-be-beauty:
    - curry compose

  - to-be-faster:
    - . xs -> xs
    - 1/2 -> 0.5
    - def-syn
    - def f g -> alias f g
    - nilp (cdr xs)
    - [] -> ()
    - (small .. big) -> (big .. small)
    - ?: setq
    - clauses should be Hz -> hz
    - def/va: case-lambda needs 1~2X time more than original lambda
    - atomp -> consp

  - to-debug:
    - (trace fib)?, assert&print, debug?, call/cc+assert+return.false ...

  - flow: work->fast->safe->complete
    - ;must-inits
    - ; main-apis
    - ;apis-for-main
    - ; apps-api
    - ;endups
    - ; test

  - common:
    - (_ X x)
    - syt -> '
    - common/special... - :
|#

;(import (chezscheme)) ;you need this when used --program
;(collect-request-handler void) ;~ for some optimizing

;(load (str *lib-path* "/match.ss"))

;#%car = ($primitive car) = car ~= #1%car = ($primitive 1 car) ; #(2~3)%car

;================= aliases and syntaxes ===================

(alias ali      alias )
(ali   imp      import)
(ali   lam      lambda)
(ali   bgn      begin )
(ali   letn     let*  )
(alias fn       lambda)
(alias progn    begin )

(alias case-lam case-lambda)
(alias def-syt  define-syntax)
(alias syt-ruls syntax-rules)
(alias syt-case syntax-case)
(alias quo      quote)
(alias els      else )

(ali   vec      vector)
(alias vec?     vector?) ;
(alias vec-len  vector-length)
(alias vec-ref  vector-ref)
(alias vec->lis vector->list) ;
(alias lis->vec list->vector) ;

(ali   exist-file? file-exists?)
(alias id       id-car)

; defaults

(ali trim   trim-left)
(ali trim-n trim-left-n)
;(alias trim-head trim-head-1)
;(alias trim-tail trim-tail-1)

; shorthands

(ali list->str  list->string)
(ali str->sym   string->symbol)
(ali str->chs   string->list)
(ali char->int  char->integer)
(ali int->char  integer->char)
(ali num->str number->string)
(ali replace  list-repl0)
(alias make-groups combinations)
(alias walk walk-lhs)
(ali round* myround)
(ali int/ quotient)

;ex
(ali range myrange)

;better

(ali folder? file-directory?)

(define-syntax define*
  (syntax-rules ()
    ( [_ x] (define x [void]) ) 
    ( [_ (g . args) body ...] 
      (define (g . args) body ...) )
    ( [_ x e] (define x e) ) ;sym? e: e *v
    ; ;The followings make def slow:
    ; ([_ g (args ...) body ...]
      ; (define (g args ...) body ...) ) ;
    ; ([_ g args body ...] ;
      ; (define (g . args) body ...) )
) )

(ali   nilp  null?)
(ali   first car)
(ali   rest  cdr)
(ali   eq    eq?)
(ali   eql   equal?)
(alias equal equal?)

(alias f-and logic-and)
(alias ==    equal?)
(alias ?: if)
;(alias ?  if)
(alias !  not)
(alias sym?   symbol?)
(alias bool?  boolean?)
(alias int?   integer?)
(alias num?   number?)
(alias str?   string?)
;(alias lisp   list?) ;nil?
(ali   consp  pair?)
(alias pairp  pair?)
(alias fn?    procedure?)
(alias voidp  void?) ;voip
(alias atomp  atom?) ;atop
(alias nump   number?)
(alias exa->inexa exact->inexact)
(alias inexa->exa inexact->exact)
(alias sym->str symbol->string)
(alias ev     eval)
(alias reduce apply) ;
(alias redu   apply) ;
(alias strcat string-append)
(alias foldl  fold-left)
(alias foldr  fold-right)
(alias mod remainder) ;
(alias %   mod) ;
(alias ceil ceiling)
(alias identities values)
(alias repl new-cafe)
(alias fmt format)
(alias exec command-result) ;
(alias sys system)
;(def (sys cmd) (zero? (system cmd)))
(alias q exit)
(alias str-append string-append)
(ali   len length)
(alias newln newline)
(alias nil?  null?)

(alias 1st car)
(alias 2nd cadr)
(alias 3rd caddr)

(ali No1 car) ;
(ali No2 cadr)
(ali No3 caddr)
(ali elap elapse)
(ali origin $primitive)

(alias head list-head) ;.
(alias redu~ redu~/fold) ;. (redu~ list '(1 2 3))
(alias strhead! string-truncate!) ;
; To put aliases here

(alias dmap deep-map)

(alias choose choose%) ;
;(alias choose true-choose)

(ali api-ls api-with)

(alias hex->int hex->dec)
(ali make-file!% make-file!%/win)
(ali make-path make-path/win)

;

(define-syntax defsyt
  (syntax-rules ()
    ( [_ f (expr body ...)] ;;one ;must be bef (_ f g)
      (define-syntax f
        (syntax-rules ()
          (expr
            (begin body ...) ) ) ) ) ;
    ( [_ f g]
      (define-syntax f
        (syntax-rules ()
          ( [_ . args] ;
            (g . args) ) ) ) )
    ( [_ f (expr ...) ...]   ;multiple
      (define-syntax f
        (syntax-rules ()
          (expr ...) ...
) ) ) ) )

(defsyt defm ;define-macro <- define-syntax ;to-add (void)
  ( [_ (f . args) body ...]
    (defsyt f ;
      ( [_ . args]
        (begin body ...) ;
  ) ) )
  ( [_ f (args ...) body ...]
    (defm (f args ...) body ...)
) )

(def-syt (if% stx)
  (syt-case stx (else) ;
    ( [_ () (bd ...)]
      #'(cond bd ...) )
    ( [_ (last-expr) (bd ...)]
      #'(if% () (bd ... [else last-expr])) )
    ( [_ (k e more ...) (bd ...)]
      #'(if% (more ...) (bd ... [k e]))
) ) )
(def-syt (if~ stx)
  (syt-case stx ()
    ([_ bd ...]
      #'(if% [bd ...] []) ;
) ) )

(defsyt defun
  ( [_ f args ...]
    (define f (lam args ...)) )
  ( [_ f args ]
    (define (f . args) *v) ) ;
)
(ali defn defun)
(ali mem? member)

(defsyt defn-nest ;(lam(a)(lam(b)(lam () body...))) ;(defnest(asd)1) must err
  ( [_ f args body ...]
    (define f
      (eval ;
        (foldr
          (lam (a b) [append~ a (li b)])
          `(lam () body ...)
          (map [lam (x) `(lam (,x))] 'args) ;
) ) ) ) )
(defsyt defn-snest ;(lam(a)(lam(b) body...))
  ( [_ f args body ...]
    (define f
      (eval
        (foldr
          [lam (a b) (append a (list b))]
          `(bgn body ...)
          (map [lam (x) `(lam (,x) )] 'args) ;
) ) ) ) )
;lam-snest (x y z) (+ x y z)

;(define-syntax _ (syntax-rules () )) ;for export
(define-syntax def_ ;i think it s good
  (syntax-rules ()
    [(_ (id . args) body ...)
      (def_ id (lambda args body ...))] ;for lambda format
    [(_ id expr)
      (define id
        (fluid-let-syntax ([_ (identifier-syntax id)]) ;
          expr
) ) ] ) )

(defsyt let/ad
  ( [_ xs code ...]
    (fluid-let-syntax ;syntax-parameter?
      ( [a (identifier-syntax (car xs))]
        [d (identifier-syntax (cdr xs))] )
      code ...
) ) )

(defsyt letn/ad
  ( [_ xs rest code ...]
    (fluid-let-syntax
      ( [a (identifier-syntax (car xs))]
        [d (identifier-syntax (cdr xs))] )
      (letn rest ;
        code ...
) ) ) )
(defsyt let/ad* ;?
  ( [_ xs rest code ...]
    (fluid-let-syntax
      ( [a (identifier-syntax (car xs))]
        [d (identifier-syntax (cdr xs))] )
      (let rest
        code ...
) ) ) )

(defsyt defn_
  ( [_$% f args bd...] ;
    (def_ (f . args) bd...)
) )

(defsyt defs ;inner
  ((_ a) (def a (void)))
  ((_ a b)
    (bgn (def a b) (if *will-ret* a)) ;
  )
  ((_ a b c ...)
    (bgn
      (def a b)
      (defs c ...) ;
) ) )

(defsyt setq ;outer
  ((_ a) (set! a (void)))
  ((_ a b)
    (bgn (set! a b) (if *will-ret* a))
  )
  ((_ a b c ...)
    (bgn
      (set! a b)
      (setq c ...) ;
) ) )

; c

(defsyt +=
  ( [_ x . xs]
    (bgn
      (set! x (+ x . xs)) ;
      x
) ) )

(defsyt -=
  ( [_ x . xs]
    (bgn
      (set! x (- x [+ . xs])) ;
      x
) ) )

;

(def-syt (append!% stx) ;
  (syt-case stx ()
    ( [_ xs . yz]
      [identifier? #'xs]
      #'(bgn
          [set! xs (append xs . yz)] ;
          xs ) )
    ( [_ . xz]
      #'(append . xz)
) ) )

;

(alias identity id)
(alias li list)

(ali str->list string->list)
;(ali str-divide string-divide)
(alias disp display*) ;
(alias displn displayln*)

(defsyt sy/num-not-defa-vals%
  ([_ () n] n)
  ([_ ((x vx)) n]       (sy/num-not-defa-vals% () n))
  ([_ (x) n]            (sy/num-not-defa-vals% () (fx1+ n)))
  ([_ ((x vx) y ...) n] (sy/num-not-defa-vals% (y ...) n))
  ([_ (x y ...) n]      (sy/num-not-defa-vals% (y ...) (fx1+ n))) ;
)
(defsyt sy/num-not-defa-vals ;good for: (_ a [b 1] c)
  ([_ . xs] (sy/num-not-defa-vals% xs 0))
)
(defsyt sy/list-the-front ;
  ( [_ ()] '())
  ( [_ ((x ...) . xs)] '((x ...) . xs))
  ( [_ (x)] (cons '(x) [sy/list-the-front ()])) ;
  ( [_ (x . xs)]
    (cons '(x) [sy/list-the-front xs]) ;
) )
;(call-with-values (lam()(values 'a 'b vc)) g) ;
(defsyt def/defa@ ;@ (_ (g [a] [b 2] [c ]) (+ a b c)) ;test on fib0 found some issue
  ( [_ (g . paras) body ...] (def/defa@ g paras body ...))
  ( [_ g paras% body ...]
    (define (g . args) ; case-lam is good
      (let ([paras (list-elements 'paras%)])
        (define f% [ev `(lam ,(map car paras) body ...)]) ; eval is not good
        (letn ( [paras-ln (len paras)]
                [num-not-defa (num-not-defa-vals paras)]
                [vals-ln (len args)] ;args for calling ; runtime args
                [n-head (- vals-ln num-not-defa)]
                [n-tail (- paras-ln vals-ln)] ) ;(echol n-head num-not-defa n-tail)
          (redu f%
            (defa->vals/aux paras [head% args paras-ln] ;
              n-head num-not-defa n-tail
) ) ) ) ) ) )
;We may def func again with some defa paras, and test the func with just one variable para.

(defsyt defn/values%
  ([_ f (p ... q) (V ... Q) ret ...]
    (defn/values% f (p ...) (V ...)
      ret ... ([p ...] (f p ... Q))
  ) )
  ([_ f (p ...) () ret ...]
    (case-lam ret ...) ;@
) )
(defsyt defn/values
  ([_ f (p ...) [V ...] body ...]
    (def f
      [defn/values% f (p ...) [V ...] ;
        ([p ...] body ...) ]
) ) )
(defsyt def/values
  ([_ (f p ...) [V ...] body ...]
    (def f
      [defn/values% f (p ...) [V ...] ;
        ([p ...] body ...) ]
) ) )
(alias defn/defa defn/values) ;

#|
(def/va%4
  asd
  ((a 1) (s s) (d 3) (f f))
  ((a 1) (s s) (d 3) (f f))
  (a d)
  ()
  (a d)
  (((a s d f) (li a s d f)))
  ()
  () )
to-test:
  (def/va (asd a b [li li]) (li a b)) ;(asd 1 2) ;--> ok
|#
(def-syt (def/va%4 stx) ;~ $ &
  (syt-case stx ()
    ;_ g, Ori-pairs para-pairs; main-cnt=(A D), Ori-tmp-cnt=() tmp-cnt=(?); Ret, lamPara=[] bodyPara=[]
    ([_           g ori-pairs ([a A] ... [z Z]) main-cnt ori-tmp-cnt [C1 C2 ...] ret [  lamPara ...] (  bodyPara ...)]
      (eq #'z #'Z)
      #'(def/va%4 g ori-pairs ([a A] ...      ) main-cnt ori-tmp-cnt [C1 C2 ...] ret [z lamPara ...] (z bodyPara ...))
    )
    ([_           g ori-pairs ([a A] ... [z Z]) main-cnt ori-tmp-cnt [C1 C2 ...] ret [  lamPara ...] (  bodyPara ...)]

      #'(def/va%4 g ori-pairs ([a A] ...      ) main-cnt ori-tmp-cnt [   C2 ...] ret [  lamPara ...] (Z bodyPara ...))
    )
    ([_           g ori-pairs ([a A] ... [z Z]) (A0 ...) ori-tmp-cnt [         ] (ret ...) [  tmp ...] (  rest ...)] ;
      #'(def/va%4 g ori-pairs ([a A] ...      ) (A0 ...) ori-tmp-cnt [         ] (ret ...) [z tmp ...] (z rest ...))
    )
    ([_           g ori-pairs (               ) (A0 B0 ...) (   ) [ ] (ret ...) [tmp ...] (rest ...)]
      #'(def/va%4 g ori-pairs ori-pairs  (   B0 ...) (A0) (A0) (ret ...) [] [])
    )
    ([_           g ori-pairs (               ) (A0 B0 ...) (   ori-tmp-cnt ...) []                   (ret ...)                         [tmp ...] (rest ...)] ;tmp
      #'(def/va%4 g ori-pairs ori-pairs         (   B0 ...) (A0 ori-tmp-cnt ...) (A0 ori-tmp-cnt ...) (ret ... ([tmp ...](g rest ...))) [] [])
    )
    ([_           g ori-pairs para-pairs        [         ] ori-tmp-cnt       [] (ret ...) [  tmp ...] (  rest ...)]
      #'(def      g (case-lam ret ... ([tmp ...] (g rest ...)) ) )
) ) )
;_ g, Ori-pairs para-pairs; main-cnt=(A D), Ori-tmp-cnt tmp-cnt=(); Ret, lamPara=[] bodyPara=[]

#|
(def/va%3
  asd
  ((a 1) s (d 3) f)
  ((a 1) (s s) (d 3) (f f))
  [a d]
  (li a s d f))
|#
(defsyt def/va%3
  ( [_ g ori [(a b) ...] (defas ...) body ...]
    (def/va%4
      g
      [(a b) ...]
      [(a b) ...]
      (defas ...) ;
      []
      (defas ...) ;<- []
      [([a ...] body ...)]
      [] []
) ) )

#|
(def/va%2 asd ((a 1) s (d 3) f) ((a 1) s (d 3) f)
  () []
  (li a s d f) )
|#
(def-syt (def/va%2 stx)
  (syt-case stx ()
    ( [_          g ori (x y ...) (ret ...      ) [  defas ...] body ...] (identifier? #'x)
      #'(def/va%2 g ori (  y ...) (ret ... [x x]) [  defas ...] body ...)
    ) ;
    ( [_          g ori (x y ...) (ret ...      ) [  defas ...] body ...]
      #'(def/va%2 g ori (  y ...) (ret ...  x   ) [x defas ...] body ...)
    )
    ( [_          g ori (       ) (ret ...      ) [  defas ...] body ...]
      #'(def/va%3 g ori           (ret ...      ) [  defas ...] body ...)
) ) )

;to do: (def/va (asd [a 1] s [d 3] f) (li a s d f)) ;=> (asd 'A 'S 'F)
;to test: (def/va (asd [a 1] [b 2] [c 3]) (li a b c)) ;(asd)
(defsyt def/va
  ( [_ (f x ...) body ...]
    (def/va%2 f (x ...) (x ...) () [] body ...) ;
) )
(defsyt defn/va
  ( [_ f (x ...) body ...]
    (def/va%2 f (x ...) (x ...) () [] body ...)
) )
(alias def/defa def/va)
;test: (def/va (sublis xs [s 0] n) [head(tail xs s)n]) (sublis '(1 2 3) 2)

(def-syt vec-for ;
  (syt-ruls (in)
    ( [_ i in ve body ...]
      (quiet ;
        (vector-map ;
          (lambda (i)
            body ... )
          ve )
) ) ) )

;(collect 20 expr)
(define-syntax collect
  (syntax-rules (in)
    ( [_ (i num) do-sth]
      (let _ ([i 0])
        (if [>= i num] nil
          (cons do-sth [_ (1+ i)]) ;
    ) ) )
    ( [_ (i in xs) body ...]
      (let loop ([l xs])
        (if (nilp l) nil
          (let ([i (car l)])
            (cons (bgn body ...) [loop (cdr l)]) ;
    ) ) ) )
    ( [_ num do-sth]
      (collect [i num] do-sth) )
) )

(define-syntax for ;(for-each g xs)
  (syntax-rules (in : as)
    ( [_ i in xs body ...]
      (let loop ([l xs])
        (unless (nilp l)
          (let ([i (car l)])
            body ...
            [loop (cdr l)]
    ) ) ) )
    ( [_ xs as i body ...]
      (for-each
        (lambda (i) ;map has ret values
          body ...)
        xs
    ) )

    ( [_ (i : xs) body ...]
      (for-each
        (lam (i)
          body ...)
        xs ) )
    ( [_ (i in xs) body ...] ;
      (for-each
        (lam (i)
          body ... )
        xs ) )

    ( [_ () b1 ...] ;;(for ((+ 2 3)) ..) ;i?
      (let loop ()
        (when T
          b1 ...
          [loop] ) ) )
    ( [_ (n) b1 ...] ;;(for ((+ 2 3)) ..) ;i?
      (let loop ([i 0])
        (when (< i n)
          b1 ...
          [loop (fx1+ i)] ) ) )

    ( [_ (i n) code ...]
      (for [i 0 (1- n)] code ... ) )
    ( [_ (i from to) code ...]
      (for (i from to 1) code ...) )
    ( [_ (i from to step) code ...]
      (let ~ ([i from])
        (cond
          ([> step 0]
            (when (<= i to)
              code ...
              [~ (+ i step)] ) )
          ([< step 0]
            (when (>= i to)
              code ...
              [~ (+ i step)] ) )
          (else nil) ;fz
    ) ) )

    ;call/cc
    ( [_ k (n) b1 ...] ;;(for ((+ 2 3)) ..) ;i?
      (let loop ([i 0])
        (call/cc
          (lam (k)
            (when [< i n]
              b1 ...
              [loop (fx1+ i)]
    ) ) ) ) )

    ( [_ k (i n) b1 ...]
      (for k (i 0 [1- n]) b1 ...) ) ;
    ( [_ k (i from to) b1 ...]
      (let loop ([i from]) ;let when
        (call/cc
          (lam (k)
            (when [<= i to]
              b1 ...
              [loop (fx1+ i)] ;
    ) ) ) ) )
    ( [_ k (i from to step) b1 ...]
      (let loop ([i from])
        (call/cc
          (lam (k)
            (cond
              ( [> step 0]
                (when (<= i to)
                  b1 ...
                  [loop (+ i step)] ) )
              ( [eq step 0] nil )
              ( [< step 0]
                (when (>= i to)
                  b1 ...
                  [loop (+ i step)]
    ) ) ) ) ) ) )
) )

(defsyt while
  ( [_ k bd ...]
    (call/cc
      (lam (break)
        (let loop ()
          (if k
            [bgn bd ... (loop)]
            (break) ;
) ) ) ) ) )

(defm (sy-redu g (x ...)) ;
  (g x ...)
)

;sy-

(defsyt sy-rev% ;
  ( [_ () (ret ...)] '(ret ...) ) ;
  ( [_ (x) (ret ...)]
    '(x ret ...) )
  ( [_ (x ys ...) (ret ...)]
    (sy-rev% [ys ...] [x ret ...]) )
)
(defsyt sy-rev
  ( [_ (xs ...)]
    [sy-rev% (xs ...) ()] )
  ( [_ xs ...]
    [sy-rev% (xs ...) ()] )
)

(defsyt lam-nest% ;(_ (a b) bd...) -> [lam(a)[lam(b) bd...]]
  ( [_ () (ret ...)]
    [ret ...] )
  ( [_ (x) (ret ...)]
    [lam (x) [ret ...]] )
  ( [_ (x ys ...) (ret ...)]
    [lam (x) (lam-nest% (ys ...) [ret ...])] ) ;
)
(defsyt lam-rnest%
  ( [_ () (ret ...)]
    [ret ...] )
  ( [_ (x) (ret ...)]
    [lam(x) [ret ...]] )
  ( [_ (x ys ...) (ret ...)]
    (lam-rnest% (ys ...) [lam(x) [ret ...]]) )
)

(defsyt lam-rnest
  ( [_ (xs ...) bd ...]
    [lam-rnest% (xs ...) [lam() bd ...]] )
)
(defsyt lam-srnest
  ( [_ (xs ...) bd ...]
    [lam-rnest% (xs ...) (bgn bd ...)] )
)
(defsyt lam-nest
  ( [_ (xs ...) bd ...]
    [lam-nest% (xs ...) [lam() bd ...]] )
)
(defsyt lam-snest
  ( [_ (xs ...) bd ...]
    [lam-nest% (xs ...) [bgn bd ...]] )
)

(alias && and)

(ali & bitwise-and) ;bits-and

(alias todo   quiet)
(alias tofix  id)
(alias ?~     if~)
(alias str-upcase   string-upcase)
(alias str-downcase string-downcase)
(ali nth-of   nth-of-x)
(ali find-x-meet  find-x-match)
(alias list/nth   list/nth-)
(defsyt set-xth!% ;chg-nth
  ( [_ xs i y]
    (letn [ (n (fx1+ i))
            (m (1- i))
            (ln (len xs))
            (pre (ncdr xs (- m ln -1))) ;
            (pos (ncdr xs n)) ]
      (set! xs (append pre (cons y pos)) ) ;
) ) )
(defsyt set-xth! ;chg-nth
  ( [_ xs i y]
    (letn [ (n (1+ i))
            (m (1- i))
            (ln (len xs))
            (pre (ncdr xs (- m ln -1))) ;
            (pos (ncdr xs n)) ] ;
      (set! xs (append! pre (cons y pos)) ) ;!
) ) )
(defsyt set-nth!
  ( [_ xs n y] (set-xth! xs (1- n) y) )
)

(defsyt insert-xth!
  ( [_ xs i y]
    (letn([pre (head xs i)]
          [pos (tail xs i)])
      (setq xs (append! pre (cons y pos))) ;
) ) )

(defsyt swap-xths!
  ( [_ xs i j]
    (let ([t (nth xs i)])
      (set-xth! xs i (nth xs j))
      (set-xth! xs j t)
  ) )
  ( [_ xs i ys j]
    (let ([t (nth xs i)])
      (set-xth! xs i (nth ys j))
      (set-xth! ys j t)
) ) )
(defsyt swap-nths!
  ( (_ xs m n)
    (swap-xths! xs (1- m) (1- n)) )
  ( (_ xs m ys n)
    (swap-xths! xs (1- m) ys (1- n)) )
)

(def-syt (pop stx)
  (syntax-case stx ()
    ( [_ xs]
      [identifier? #'xs]
      #'(let ([ret (car xs)])
        [set! xs (cdr xs)]
        ret ) )
    ( [_ xs]
      #'(car xs)
) ) )

(def-syt (push stx)
  (syntax-case stx () ;
    ( [_ args ... x]
      (identifier? #'x) ;
      #'(setq x (cons* args ... x)) ) ;
    ( [_ . args]
      #'(cons* . args)
) ) )

; to make return similar to bgn/values, with multiple input values

(def-syt (rpush stx)
  (syt-case stx ()
    ( [_ args ... xs]
      (identifier? #'xs)
      #'(bgn
        (if [nilp xs]
          (setq xs (li args ...))
          (set-cdr! (last-pair xs) (li args ...)) ) ;@
        (return xs)
    ) ) ;
    ( [_ args ... xs]
      #'(if [nilp xs]
        (setq xs (li args ...)) ;
        (bgn
          (set-cdr! (last-pair xs) (li args ...)) ;let ([xs xs]) ?
          (return xs)
) ) ) ) )


(defsyt type-main ;todo detail for printf ;symbol uses eq is betta
  ( [_ x]
    (cond
      ;((ffi-s? (any->str 'x))  "ffi") ;x if not sym
      ((symbol?  x)   'symbol) ;
      ((bool? x)      'boolean)
      ((number?  x)   'number) ;
      ((char? x)      'char) ;
      ((string?  x)   'string) ;
      ((nilp  x)      'null)
      ((list? x)      'list) ;
      ((pair? x)      'pair)
      ;((ffi?  x)     'ffi) ;
      ((fn?   x)      'fn) ;procedure
      ((vector? x)    'vector) ;
      ((void? x)      'void)
      ((atom? x)      'other-atom) ;(eof-object) ;x (void) #err
      (else           'other)  ;other-atoms
) ) )
(alias ty type-main)

;
(defm (raw . xs) ;(str '|c:\asd\|)
  (if~
    (nilp 'xs) nil
    (cdr-nilp 'xs)
      (car 'xs)
    'xs
) )

(alias lis2num list->num)
(ali xn->list xn-mk-list)
;cl

(alias atom atom?)
(alias null null?)
(alias second cadr)

;

(defsyt getf
  ( (_ xs xtag)
    (if [< (len xs) 2] nil
      (if [eq (car xs) 'xtag]
        (cadr xs)
        (ev `(getf (cddr xs) xtag)) ;
) ) ) )

(defsyt getf-xth-iter
  ( (_ x f1 i)
    (if (< (len x) 2) nil ;
      (if (eq (car x) 'f1)
        (fx1+ i)
        (ev `(getf-xth-iter (cddr x) f1 (+ 2 i))) ;
) ) ) )

(defsyt getf-xth
  ( (_ x f1)
    (getf-xth-iter x f1 0)
) )

(defsyt setf* ;(_ mapA tagX a)
  ( [_ x f1 a]
    (let ([i (getf-xth x f1)]) ;
      (if [nilp i]
        (if *will-ret* x nil)
        (set-xth! x i a) ;
) ) ) )

(alias aref list-ref) ;

;oth
(alias op-inp-str open-input-string)
(alias str->ss str-explode)


;C

;(alias ref list-ref)

;lisp use quo and defsyt, instead of get-addr in c
(defsyt swap
  ( [_ a b]
    (if (eql a b)
      nil
      (let ([t a])
        (setq a b  b t)
    ) )
    (li a b)
) )

(alias rev! reverse!)
(alias d-len deep-length) ;d-cnt
(defm (assert resl test)
  (letn ([tmp resl] [b(eql tmp test)]
      [ret(if b 'Ok 'Wrong!!)] [ss `(resl " expect " test " ---> " ,ret)] )
    (redu echo ss) ;
    (newln)
) )
(alias =0 =0?)
(alias =1 =1?)
(alias len0 len0?)
(alias quot quotient)
(alias permu permutation)
(ali deep-rev  deep-reverse)

;onlisp

(def-syt [nreverse! stx]
  (syntax-case stx ()
    ( [_ xs]
      [identifier? #'xs]
      #'(let ([tmp (rev xs)])
        (set! xs (li(car xs)))
        tmp
    ) )
    ( [_ xs]
      #'(rev xs) )
) )

(ali list-divide-per group)
(ali map-all map-for-combinations)

(ali fast-expt/x0 fast-expt-algo)
;

(ali list-include flat-list-include)
;



(alias != not=)
(alias >> bitwise-arithmetic-shift-right)
(alias << bitwise-arithmetic-shift-left)
(alias inexa inexact)
(ali nbits n-digits)
(ali mat-unitlen matrix-unitlen)
(ali mat-unit   matrix-unit)
(ali mat-unitof matrix-unitof)
(ali mat-mul matrix-mul)
(ali mat-pow matrix-pow)
(ali lis2mat group) ;(lis2mat '(1 2 3 4 5) 2) -> ((1 2) (3 4) (5 0))?
(ali mat2lis flat)

(ali mat-ref xth)
(ali mat-1Muln pt-mat-mul)
(ali mat-nMuln mat-mat-mul)
(alias relu ReLU)
(alias diagonalength diagonal-length)
(defm (quine g) `(,'g ,'g)) ;
(alias exception? condition?)
(alias try-fail? condition?)
(ali bad-try? condition?)
(alias ev-full full-eval)


(alias float inexact)

(alias num->bump-g num->rbump-g)
(alias num->bump num->rbump)


;vec@: mk-vec n; vec-fill!; vec-set! v i x;

(ali vec-len  vector-length)
(ali mk-vec   make-vector)
(ali vec-copy vector-copy)
(ali vec-set-fnum! vector-set-fixnum!)
(ali vec-set! vector-set-fixnum!)
(ali vecar    vec-car)

(def-syt (ve-push* stx)
  (syt-case stx () ;
    ( [_ args ... x]
      (identifier? #'x) ;
      #'[setq x (ve-cons* args ... x)] ) ;mk-vec will slower than list's
    ( [_ . args]
      #'(ve-cons* . args)
) ) )

(alias vnilp vec-nilp)
(alias vecons vec-cons)
(alias veconz vec-conz)
(alias vecdr vec-cdr)

(defsyt try ;rkt: option, some ?
  ( [_ exp]
    (guard [x (else x)] exp) ) ;(condition? #condition) -> T
  ( [_ exp value-for-err]
    (guard [x (else value-for-err)] exp)
) )

;(def asd (lam/lams ([(a) b] . xs) [append (list a b) xs])) ([(asd 1) 2] 3 4)
(def-syt (lam/lams stx)
  (syt-case stx ()
    ( [_ () body ...]
      #'(lam () body ...) )
    ( [_ (a . xs) body ...] (identifier? #'a)
      #'(lam (a . xs) body ...) )
    ( [_ (a . xs) body ...]
      #'[lam/lams a (lam xs body ...)]
) ) )

; htab 1/2

;(mk-htab htab (list ))
(defsyt mk-htab ;!
  ( [_ var init] ;key-eq?]
    (if (exception? (try var))
      (setq var init)
      nil ;(error "existed" 'var)
) ) )

(defsyt add-to-htab
  ( [_ ht child ret-if-exist]
    (let ([key (car child)])
      (def (_ ht) ;
        (if (eq key (caar ht))
          ret-if-exist
          (if (cdr-nilp ht)
            (set-cdr! ht (list child)) ;add/rpush
            [_ (cdr ht)]
      ) ) )
      (if (nilp ht)
        (setq ht (list child)) ;init
        [_ ht]
  ) ) )
  ( [_ ht child]
    (add-to-htab ht child (error "existed" (car child))) ;F
) )

(defsyt add-to-htab!
  ( [_ ht child]
    (let ([key (car child)])
      (def (_ ht)
        (if [eq key (caar ht)]
          (set-car! ht child) ;update!
          (if [cdr-nilp ht]
            (set-cdr! ht (list child)) ;add/rpush
            [_ (cdr ht)]
      ) ) )
      (if (nilp ht)
        (setq ht (list child)) ;init
        [_ ht]
) ) ) )

;X(car body) if-is string, save to (doc)
(defsyt def/doc
  ( [_ x] (define x *v) )
  ( [_ (g . args) body ...]
    (bgn
      (add-to-htab! *htab/fn-lam* `,[raw (g (lam args body ...))]) ;bef def?
      (define (g . args) body ...)
  ) )
  ( [_ x e]
    (bgn
      (add-to-htab! *htab/fn-lam* `,[raw (x e)])
      (define x e) ;(def& x e last-action?)
) ) )
;doc-code doc-paras

(ali def define*)


;(doc f-asd)
(defsyt doc-paras
  ( [_ key] ;if fn? key
    (doc-paras% ;<- htab-value
      (if (htab/fn-lam?) *htab/fn-lam* *htab/fn-doc*)
      'key
  ) )
  ( [_ key htab]
    (doc-paras% htab 'key) ;<- doc%
) )

(defsyt doc-code ;-value -keys
  ( [_ key] ;if fn? key
    (htab-value ;<- htab-value
      (if (htab/fn-lam?) *htab/fn-lam* *htab/fn-doc*)
      'key
  ) )
  ( [_ key htab]
    (htab-value htab 'key) ;<- doc%
) )

(defsyt doc-main
  ( [_ key]
    (htab-kv
      (if (htab/fn-lam?) *htab/fn-lam* *htab/fn-doc*)
      'key
  ) )
  ( [_ key htab]
    (htab-kv htab 'key)
) )

(ali doc doc-main)

;(doc-ls co) -> documentable-keys -> '(cons cond)
(defsyt doc-ls
  ( [_ contain htab] ;defm/va
    (filter (rcurry with?-nocase 'contain)
      (map car (docs-main htab)) ;
  ) )
  ( [_ contain]
    (doc-ls contain [if (htab/fn-lam?) *htab/fn-lam* *htab/fn-doc*]) ;
) )


; pattern matching

(define-syntax list-match
  (syntax-rules ()
    ( (_ expr (pattern fender ... template) ...)
      (let ((obj expr))
        (cond
          ( [list-match-aux obj pattern fender ...
              (list template)] => car) ...
          ( else (error 'list-match "pattern failure") )
) ) ) ) )

(define-syntax list-match-aux
  (lambda (stx)
    (define (underscore? x)
      (and (identifier? x) (free-identifier=? x (syntax _))))
    (syntax-case stx (quote quasiquote)
      ( (_ obj pattern template)
        (syntax (list-match-aux obj pattern #t template)))
      ( (_ obj () fender template)
        (syntax (and (null? obj) fender template)))
      ( (_ obj underscore fender template)
        (underscore? (syntax underscore))
        (syntax (and fender template)))
      ( (_ obj var fender template)
        (identifier? (syntax var))
        (syntax (let ((var obj)) (and fender template))))
      ( (_ obj (quote datum) fender template)
        (syntax (and (equal? obj (quote datum)) fender template)))
      ( (_ obj (quasiquote datum) fender template)
        (syntax (and (equal? obj (quasiquote datum)) fender template)))
      ( (_ obj (kar . kdr) fender template)
        (syntax (and (pair? obj)
                (let ((kar-obj (car obj)) (kdr-obj (cdr obj)))
                  (list-match-aux kar-obj kar
                        (list-match-aux kdr-obj kdr fender template))))))
      ( (_ obj const fender template)
        (syntax (and (equal? obj const) fender template))))))

(defsyt cost
  ( [_ g echo?]
    (let ([t 0] [res nil])
      (if echo? (echol (fmt ": ~s" 'g))) ;
      ;(set! t (clock))
      (set! t (get-ms)) ;
      (set! res g)
      ;(set! t (inexa(/ (-(clock)t) CLOCKS_PER_SEC)))
      (set! t (- (get-ms) t))
      (if echo? (echol ": elapse =" t "ms")) ;
      (list res t)
  ) )
  ( [_ g]
    (cost g T)
) )

(defsyt elapse ;just elapse but result
  ( [_ g]
    (let ([t 0])
      (echol (fmt ": ~s" 'g))
      ;(set! t (clock))
      (set! t (get-ms)) ;
      g
      ;(set! t (inexa(/ (-(clock)t) CLOCKS_PER_SEC)))
      (set! t (- (get-ms) t)) ;
      (echol ": elapse =" t "ms")
      t
) ) )

;Code written by Oleg Kiselyov

(def-syt ppat ;ppattern for ?
  (syt-ruls (if comma unquote quote) ;comma for unquo?
    ([_ v ? kt kf] kt)
    ([_ v () kt kf] (if (nilp v) kt kf))
    ((_ v (quote lit) kt kf) (if (equal? v (quote lit)) kt kf)) ;x?
    ([_ v (unquote var) kt kf] (let ([var v]) kt))
    ([_ v (x . y) kt kf]
      (if (pair? v)
        (let ([vx(car v)] [vy(cdr v)])
          (ppat vx x (ppat vy y kt kf) kf) )
        kf
    ) )
    ([_ v lit kt kf] (if [equal?(quote lit)v] kt kf))
) )
;(ppat '(1 b) (,a b) *t *f)
;(ppat '(2 3) (,a ,b) b *f)

(def-syt pmatch-aux
  (syt-ruls (else guard)
    ([_ name (rator rand ...) cs ...] ;rator rand
      (let ([v (rator rand ...)])
        (pmatch-aux name v cs ...) )) ;cs?
    ([_ name v] ;err-case
      (bgn
        (if 'name
          (printf "pmatch ~s failed\n~s\n" 'name v)
          (printf "pmatch failed\n ~s\n" v))
        (error 'pmatch "match failed")
    ) )
    ((_ name v [else e0 e ...]) (bgn e0 e ...))
    ((_ name v [pat (guard g ...) e0 e ...] cs ...) ;pat for pattern
      (let ([fk (lam() (pmatch-aux name v cs ...))])
        (ppat v pat
          (if(and g ...) (bgn e0 e ...) (fk))
          (fk)
    ) ) )
    ((_ name v [pat e0 e ...] cs ...)
      (let ([fk (lam() (pmatch-aux name v cs ...))])
        (ppat v pat (bgn e0 e ...) (fk))
) ) ) )

(def-syt pmatch ;~= aux ;p for pat
  (syt-ruls (else guard)    ;guard for ?
    ([_ v      (e ...) ...]
      (pmatch-aux  *f  v (e ...) ...) )
    ([_ v name (e ...) ...] ;v for xsValue, name for aux-info
      (pmatch-aux name v (e ...) ...)
) ) )
;


(ali chk fix-chk)
;(chk 10 cdr '(1 2 3))
(defm (api? x) (bool [mem? 'x (syms)]))

;https://cisco.github.io/ChezScheme/csug9.5/summary.html#./summary:h0
(defm (api-with . xs) ;
  (let ~ ([ret (syms)] [ys 'xs]) ;
    (if (nilp ys) ret
      (let/ad ys
        (~ [filter (rcurry with-sym? a) ret] d) ;
) ) ) )
;(api-ls delete file) -> '(delete-file ...)

; complex-syntax

(define-syntax define-c-function
  (lambda (x)
    (define gen-id
      (lambda (k value)
        (datum->syntax k ;
          (string->symbol
            (id
              (let ([v (syntax->datum value)]) ;datum
                [if (string? v) v (symbol->string v)]
    ) ) ) ) ) )
    (syntax-case x () ;
      ( [k cfnam (In ...) Ret]
        (with-syntax ([name (gen-id #'k #'cfnam)]) ;
         #'(define name ;
            (foreign-procedure [if (string? 'cfnam) 'cfnam (symbol->string 'cfnam)]
              (In ...) Ret
      ) ) ) )
) ) )

(alias clean restore)
(ali *tab/jp* *tab/jp/key-a-A*)

; (defsyt lam-snest
  ; ([x] nil)
; )

(alias callnest  call-nest)
(alias callsnest call-snest)

(defsyt setf! ;no much use
  ((_ x) (set! x (void)))
  ((_ x a) (set! x a)) ;setq
  ([_ x cxr v]
    (let ([setter (case 'cxr ('cdr set-cdr!) (else set-car!))]) ;
      (setter x v)
  ) )
  ([_ x cxr cxrs ... v]
    (setf! (cxr x) cxrs ... v)
) )
;(setq xs '(1 (2))) (setf! xs cdr car 3)

; system

; time

(def (get-time)
  (letn
    ( [date (current-date)]
      [hr (date-hour date)] [m (date-minute date)] [sec (date-second date)] )
    (list hr m sec)
) )

;(time->sec (get-time))
(def/va (time->sec time [factors '(60 60 1)])
  (def (~ ret xs facs)
    (if [nilp xs] ret
      (let/ad xs
        (if [nilp facs]
          (foldl + ret xs)
          (let ([af (car facs)] [df (cdr facs)])
            [~ (* [+ a ret] af) d df]
  ) ) ) ) )
  (~ 0 time factors)
)

;ffi

(ali load-lib load-shared-object)
(ali ffi? foreign-entry?) ;
(alias ffi foreign-procedure)

;CFName nArgs tyRet fname? ;(defc Beep (void* void*) bool [beep]) ;(api: Beep 2 bool [])? ;(fname-sym CFName)
;(_ fname (var1 var2) ret FName (void* void*))
;(_ bool Beep (freq=1047 dura))

(defsyt defc*
  ( [_ f]
    (defc* f (void)) ) ;
  ( [_ f args]
    (defc* f args void*) ) ;
  ( [_ f args ret] ;defa
    (defc* f args ret f) ) ;
  ( [_ api args ret f] ;f is case-sensitive ;how many args ;void* is ok too ;no ret is ok too ;
    (def f (ffi (sym->str 'api) args ret)) ) ;outer-proc ;todo f?
  ( [_ api args ret f rems]
    (defc* api args ret f)
) )

;[x] (def-ffi (c-asd a s d) [bool Asd (int char bool)] "usage")
;[x] (def-ffi c-asd [bool Asd (int char bool)] "usage")
;[x] (def-ffi (bool Asd [int char bool]) "usage")
;[x] (def-ffi (Asd (int char bool)) "usage")
;[x] (def-ffi Asd "usage")
;(_ "BOOL sndPlaySound(LPCSTR lpszSound, UINT fuSound)")
;-> '(_ (snd-play-sound lpszSound fuSound) (bool sndPlaySound (string int)) nil "BOOL sndPlaySound(LPCSTR lpszSound, UINT fuSound)")
;(def-ffi (snd-play-sound lpszSound fuSound) (bool "sndPlaySound" (string int)))
(defsyt def-ffi
  ( [_ (f . xs) (ty-ret api ty-args) body ...]
    (def f   (ffi (sym->str 'api) ty-args ty-ret)) )
  ( [_ f        (ty-ret api ty-args) comment ...]
    (def f   (ffi (sym->str 'api) ty-args ty-ret)) )

  ( [_ f (api ty-args) comment ...]
    (def f   (ffi (sym->str 'api) ty-args void*)) )
  ( [_ (ty-ret api ty-args) comment ...]
    (def api (ffi (sym->str 'api) ty-args ty-ret)) )
  ( [_ (api ty-args) comment ...]
    (def api (ffi (sym->str 'api) ty-args void*)) ) ;

  ( [_ f comment ...]
    (def-ffi f (void* f (void))) ;
) )

(defsyt defc
  ( [_ ret f args]
    (def f (ffi (sym->str 'f) args ret)) )
  ( [_ fnam ret api args] ;
    (def fnam (ffi (sym->str 'api) args ret)) )
  ( [_ fnam rems ret api args]
    (defc fnam ret api args) )
  ( [_ fnam rems ret api args flg]
    (def fnam (ffi flg (sym->str 'api) args ret))
) )
;(defc (fnam . paras) [bgn (flg ret-type (para-types) others) (fnam [handled x] . res)])

;(alias sleep c-sleep)

(alias numofMidiOut midi-out-get-num-devs)
(ali tail list-tail)

;===================== defs =======================

(def    *f   #f)
(def    *t   #t)
(def    *v   (void))
(def    *e   '[(err)]) ;
(def    nil  '()) ;
(def    nilstr "")
(def    T    #t)
(def    F    #f)
(def    No   *f)
(def    Yes  *t)
(def    spc  " ")
(define Void *v)
(define Err  *v) ;
(def (void*) (call/cc (lam (k) (k)))) ;

;

(def *will-ret*   #t)
(def *will-disp*  #t)

; doc 1/2 flag

(define (htab/fn-lam?) T) ;

(if (htab/fn-lam?)
  (mk-htab *htab/fn-lam* nil) ;
  (mk-htab *htab/fn-doc* nil)
)

;===

;(def (id x) x)
;(def (id x . xs) x)
;(id-cadr 1 2 3)
;(id/f cadr 1 2 3) ;~> 2
(def (id-car x . xs) x)
(def (id/f f . xs) (f xs)) ;id-with-getter

(def/va (doc-add kv [db *htab/fn-lam*])
  (add-to-htab! db kv)
)

(def append!.ori append!) ;
(def (append! xs . yz) ;?
  (def (_ xs yz)
    (if (nilp yz) xs
      (if (nilp xs)
        (append!% xs [_ (car yz) (cdr yz)]) ;
        (bgn
          (set-cdr! (last-pair xs) [_ (car yz) (cdr yz)])
          xs
  ) ) ) )
  (_ xs [remov-nil yz]) ;when to ys/cons/append!/set-cdr!
)

(def (curry g . args) ;
  (lam xs
    (redu g ;
      (append~ args xs) ;
) ) )
(def (rcurry g . args)
  (lam xs
    (redu g
      (append~ xs args)
) ) )

(def (curry~ g . args)
  (lam xs
    (redu~ g ;
      (append~ args xs)
) ) )
(def (rcurry~ g . args)
  (lam xs
    (redu~ g
      (append~ xs args)
) ) )

(def void? (curry eq *v))
(def (str/pair? x) [or(string? x)(pair? x)]) ;x
(def (str/pair/vec? x) [or (string? x)(pair? x)(vector? x)]) ;for eql/eq

(def car.ori car)
(def cdr.ori cdr)
(def (car% xs)
  (if (consp xs)
    (car xs) ;.ori
    Err
) )
(def (cdr% xs)
  (if (consp xs)
    (cdr xs)
    Err
) )

;

(def (display* . xs) (display*% xs))

(def (display*% xs)
  (def (_ xs)
    (if (nilp xs) *v ;
      (bgn
        (display (car xs)) ;write/pretty-print/display/?
        [_ (cdr xs)]
  ) ) )
  ;(if *will-disp*
    (_ xs)
) ;)

(def (displayln* . xs)
  (display*% xs) (newline)
)

(def (ok? x)
  (if [or (nilp x) (fal? x)] F
    T
) )

(def [please-return!] (setq *will-ret* T))
(def [dont-return!]   (setq *will-ret* F))

(def (return x)
  (if *will-ret* x
    (if (ok? x) 'OK
      'FAIL
) ) ) ;DONE->OK FAIL

(def (set-alp! pr x)
  (set-car! (last-pair pr) x)
)
(def (set-dlp! pr x)
  (set-cdr! (last-pair pr) x)
)

;

(def [conz xs . ys] ;
  (if (nilp ys) xs
    (append xs ys) ;! a a -> cycle ;
) )
;(alias conj conz)


;(_ '(a [b 2] [c])) ;-> 2
(defn num-not-defa-vals (paras)
  (def (_ paras n)
    (if (nilp paras) n
      (let ([a (car paras)][d (cdr paras)])
        (if (consp a) ;
          (if (nilp (cdr a)) ;<-atomp
            [_ d (1+ n)]
            [_ d n] )
          [_ d (1+ n)]
  ) ) ) )
  (_ paras 0)
)
(def (list-elements xs) ;(_ '(a (b) (c 1) d)) ~> '((a) (b) (c 1) (d))
  (def (_ xs)
    (if (nilp xs) nil
      (let ([a (car xs)])
        (if (sym? a) ;consp lisp sym?
          (cons (li a) [_ (cdr xs)])
          (cons a [_ (cdr xs)]) ;
  ) ) ) )
  (_ xs)
)
(def (list-the-front xs) ;partly ;(_ '(a (b) (c 1) d)) ~> '((a) (b) (c 1) (d)) ~> '((a) (b) (c 1) (d nil))
  (def (_ xs)
    (if (nilp xs) nil
      (let ([a (car xs)])
        (if (sym? a) ;consp lisp sym? ?
          (cons (li a) [_ (cdr xs)]) ;
          xs ;
  ) ) ) )
  (_ xs)
)
; (def (defa->vals/aux paras vals nths-defa-part nths-not-defa nths-defa-rest) ;
  ; (def (_ paras vals n-head n-ndefa n-tail ret)
    ; (if (nilp paras)  ret ;
      ; (let ([ev-cadr (lam (xs) [ev(cadr xs)])])
        ; (if (nilp vals)
          ; [_ nil nil 0 0 0 [append~ (rev ret) (map ev-cadr paras)]] ;
          ; (letn ([a (car paras)] [d (cdr paras)])
            ; (if (cdr-nilp a)
              ; (cons (car vals) [_ d (cdr vals) n-head (1- n-ndefa) n-tail ret]) ;
              ; (if (<1 n-head)
                ; [_ d vals 0 n-ndefa (1- n-tail) (cons(ev[cadr a])ret)] ;
                ; (cons (car vals) [_ d (cdr vals) (1- n-head) n-ndefa n-tail ret]) ;
  ; ) ) ) ) ) ) )
  ; [_ paras vals nths-defa-part nths-not-defa nths-defa-rest nil]
; )
(def (defa->vals/aux paras vals numof-defa-vals numof-not-defa numof-defa-rest) ;@
  (def (_ paras vals n-head n-ndefa n-tail ret)
    (if (nilp paras) (rev ret)
      (let ([ev-cadr (lam (xs) [ev(cadr xs)])])
        (if (nilp vals)
          [append~ (rev ret) (map ev-cadr paras)] ;ev for eg: nil->'()
          (let ([a (car paras)] [d (cdr paras)])
            (if (cdr-nilp a) ;not-defa
              [_ d (cdr vals) n-head (1- n-ndefa) n-tail (cons (car vals) ret)]
              (if (<1 n-head)
                [_ d vals 0 n-ndefa (1- n-tail) (cons (ev-cadr a) ret) ] ;
                [_ d (cdr vals) (1- n-head) n-ndefa n-tail (cons (car vals) ret)]
  ) ) ) ) ) ) )
  [_ paras vals numof-defa-vals numof-not-defa numof-defa-rest nil]
)
;(defa->vals/aux% '((a)(b 3)(c)) '(2 4) 0 2 1) -> '(2 3 4)

;common

(def (redu~/fold g xs) ;-> curry/compose~ ;elements of xs must be simular
  (if (nilp xs) (g)
    (foldl g (car xs) (cdr xs)) ;wrong sometimes: values map echo ;echo ~> '(*v) ;evs ;i/o
) ) ;curry?


;

(def (compose . gs) ;@
  (def [_ ret gs]
    (if
      [nilp (cdr gs)] ;
        (lam xs (ret [apply (car gs) xs])) ;
      (_
        (lam (x) (ret [(car gs) x]))
        (cdr gs)
  ) ) )
  (if (nilp gs) id
    [_ id gs] ;values?
) )

(def floor->fix
  (lam (flo) (flonum->fixnum(inexact flo))) )

; todo: (_ + 2 * 3) (_ f a g b ...)
; (def (compose-fx . fxs) ;see to compose and xn-mk-list
  ; (_ (curry [car fxs] [cadr fxs]) [cddr fxs])
; )

(def (compose-n . xs) ;f m g n ...
  (redu compose
    (xn-mk-list% xs)
) )

; (def (map2 g xs yz)
  ; (def (_ xs ys zz)
    ; (if (nilp zz) (map g xs ys)
      ; [_ ]
  ; ) )
  ; (let ([yz2 (remov-nil yz)]
    ; (if (nilp yz2) nil
      ; (if (nilp xs)
        ; (_ xs (car yz2) (cdr yz2))
; ) ) ) )

(def map*
  (case-lam
    ([g xs]   (map g xs))
    ([g . xz] (redu~ (curry map g) xz)) ;(_ + '() '(1)) => '(1)
    (else     nil)
) )


(def (len* x)
  ( (if~
      [str? x] string-length
      [vec? x] vector-length
      [num? x] (rcurry nbits 10)
      length )
    x
) )
(def len%
  (case-lam
    [(x) (len* x)]
    [(x base)
      ;(if (nump x)
        (nbits x base) ;)
    ]
) )

;strcat
; (def (strcat% ss)
  ; (def (_ ss ret)
    ; (if (nilp ss) ret
      ; [_ (cdr ss) [append~ (string->list (car ss)) ret]]
  ; ) )
  ; (list->string (_ ss nil)) ;(list->string [append% (map string->list ss)])
; )

(def (nstrs s n)
  ;(redu strcat (xn2lis s n))
  [list->string (nlist% (string->list s) n)]
)

(def string-divide
  (case-lam
    ( [s sep] ;to supp, such as: sep="; "
      (if (eql "" sep)
        [str->ss s] ;
        (let
          ( [chs (str->list s)]
            [csep (car (str->list sep))] ) ;car?
          (def (rev->str chs)
            (list->str [rev chs]) )
          (def (_ chs tmp ret) ;tmp is good
            (if [nilp chs]
              (cons [rev->str tmp] ret)
              (let ([a (car chs)]) ;a?
                (if (eq a csep) ;eq?
                  [_ (cdr chs) nil (cons [rev->str tmp] ret)] ;
                  [_ (cdr chs) (cons a tmp) ret]
          ) ) ) )
          [rev (_ chs nil nil)]
    ) ) )
    ( [s] (string-divide s " ") )
) )

;seps
(def/va (str-divide ss [sep " "]) ;@
  (let ([conv str->list])
    (map list->str [divide (conv ss) (conv sep)])
) )

(define (list->revstr chs) ;lis->revstr
  (list->string (rev chs))
)
(define (string-divide-rhs-1 s sep) ;todo: str-sep
  (if (eq? "" sep) [str->ss s]
    (if (eq? "" s) "" ;
      (let ([chs(string->list s)] [csep(car(string->list sep))]) ;
        (define (_ chs ret)
          (if (null? chs) (list "" [list->string ret]) ;
            (let ([a (car chs)]) ;
              (if [eq? a csep] ;
                (list [list->revstr chs] [list->string ret]) ;
                [_ (cdr chs) (cons a ret)]
        ) ) ) )
        [_ (rev chs) '()]
) ) ) )

(def (string->path-file s)
  (string-divide-rhs-1 s "/")
)

(def (str/sep sep . sz)
  (strcat/sep sz sep)
)

(def (str/sep% sep xs) ;nil->""
  (def (_ chz ret)
    (if (nilp chz) ret
      (let ([a (car chz)])
        (if (nilp a)
          [_ (cdr chz) ret]
          [_ (cdr chz) (append a (cons sep ret))] ;.
  ) ) ) )
  (if [nilp xs] ""
    (let ([chz (rev (map [compose string->list str] xs))]) ;
      (str (_ [cdr chz] [car chz]))
) ) )

(def (str/sep~ sep . ss) ;(redu (curry str/sep " ") (map str '(123 456 789)))
  (def (_ chz ret)
    (if (nilp chz) ret
      (let ([a (car chz)])
        (if [nilp a]
          [_ (cdr chz) ret]
          [_ (cdr chz) (append a (cons sep ret))] ;.
  ) ) ) )
  (let ([chz [rev (map string->list ss)]]) ;
    (str (_ [cdr chz] [car chz]))
) )


(def (num2nth n)
  (str n
    (case (mod n 10)
      (1 "st")
      (2 "nd")
      (3 "rd")
      (else "th")
) ) )

(def (num2mon n) ;int
  (let ([mons '(Jan Feb Mar Apr May Jun Jul Aug Sep Oct Nov Dec)])
    (if~ (> n 12) nil
      (< n 1) nil
      (str (list-ref mons [1- n]))
) ) )

;

(def (append% xz)
  (def (_ xs yz)
    (if (nilp yz) xs
      (if (nilp xs)
        [_ (car yz) (cdr yz)]
        (cons (car xs) [_ (cdr xs) yz])
  ) ) )
  (let ([xz-new (remov-nil xz)])
    (_ (car xz-new) (cdr xz-new)) ;
) )

(def (append~ . xz)
  (apply append (remov-nil xz))
)

;(append/rev-head (range 5 1 - 1) (range 6 10))
(def (append/rev-head xs ys) ;rev xs then append
  (def (_ ys xs)
    (if (nilp xs) ys
      [_ (cons (car xs) ys) (cdr xs)]
  ) )
  (_ ys xs)
)

; (defn conz! (xs . ys) ;->syn
  ; (set-cdr! (last-pair xs) ys)
  ; xs
; )


(def (cls) [for (42) (newln)])

;



;

(def (last pr)
  (car (last-pair pr))
)

(def (last* xs)
  (if (nilp xs) Err
    (last xs)
) )

(def (last% xs)
  (def (_ xs)
    (if [nilp (cdr xs)]
      (car xs)
      [_ (cdr xs)]
  ) )
  (if (nilp xs) Err ;
    (_ xs)
) )

;(list/merge `(,nil a ()) `(x b () z) (lam (x y) [if (nilp x) y x]))
(def/va (list/merge xs ys [f-sel (lam (x y) [if (nilp x) y x])])
  (def (~ ret xs ys)
    (if (nilp xs)
      [append (rev ret) ys]
      (if (nilp ys)
        [append (rev ret) xs]
        (let/ad xs ;(let/ad- ys y
          (let ([ay(car ys)] [dy(cdr ys)])
            [~ (cons (f-sel a ay) ret) d dy]
  ) ) ) ) )
  (~ nil xs ys)
)

(define windows?
  (case [machine-type]
    ((a6nt i3nt ta6nt ti3nt) #t)
    (else #f)
) )


;quo/sym-

(def (sym-redu sym-f xs) ;(quo-redu 'setq '(a 1))
  (ev (cons sym-f xs)) ;
  ;(ev `(sym-f ,@xs)) ;map-q 1st-q
)

;

(def (quiet . xs) xs *v)

(defn str-mapcase% (mf s)
  (list->string (map mf (string->list s))) ;
)

(def (swap-para g) ;@ ;rev
  (lam xs
    (redu g (rev xs))
) )

; (defsyt cons~
  ; ([_ xs ...] ;[_ 1 2 3 '(4)] ~> [~ '(4) 3 2 1]
    ; (redu cons* (sy-rev xs ...))
; ) )

(def [num-of x db] ;
  (let ([g (eq/eql x)])
    (def (_ db n)
      (if [nilp db] n
        (_ (cdr db)
          (if [g (car db) x]
            (fx1+ n)
            n
    ) ) ) )
    (_ db 0)
) )

(def/va (nth-of-x x db [base 1])
  (let ([g (eq/eql x)])
    (def (_ db n)
      (if (nilp db) F
        (if [g (car db) x] n
          (_ (cdr db) (fx1+ n))
    ) ) )
    (_ db base) ;
) )

;conv

;(capitalize "asd") ;-> "Asd"
(def/va (cap-upcase ss [x->list str->list] [list->x list->str]) ;
  (let/ad [x->list ss] ;part?
    [list->x (cons (char-upcase a) d)]
) )

; list

(def (rconz ys x) ;?
  (cons z ys)
)
(def (rlist . rs)
  (rev rs)
)
(def (rcons z xs)
  ; (let ([ys (list-copy xs)]) ;
    ; (set-cdr! (last-pair ys) (cons z nil)) ;
    ; ys )
  (conz xs z) ;a bit faster than above
)

;(rmap - '(1 2) '(3 4))
(def (rmap f . xz) ;map% f (rev xz)
  [redu map (cons f (rev xz))] ;1.6X@ than map
)

(def (~map1 g xs) ;~
  (def (~ ret xs)
    (if [nilp xs] ;
      ret
      [~ (cons [g (car xs)] ret) (cdr xs)] ;
  ) )
  (~ nil xs)
)

;(map1/nths (lam (x) (list x)) '(1 2 213 123) '(2 4) F) ;-> '(1 [2] 213 [123])
(def/va (map1/nths f xs nths [sort-nths? T])
  (let ([nths (if sort-nths? (qsort nths) nths)])
    (def (~ ret xs i n nths)
      (if [nilp xs] (rev ret)
        (let/ad xs
          (if [eq n i]
            (if [nilp nths]
              (append/rev-head (cons (f a) ret) d) ;
              [~ (cons (f a) ret) d (1+ i) (car nths) (cdr nths)] ) ;
            [~ (cons a ret) d (1+ i) n nths]
    ) ) ) )
    (if [nilp nths] xs
      (~ nil xs 1 (car nths) (cdr nths)) ;
) ) )

;(head-tail (range 10) 6) ;-> '([0 1 2 3 4 5] [6 7 8 9])
(def (head-tail% xs m)
  (def (_ tmp xs m) ;xs tmp m
    (if~
      (or [nilp xs] [fx< m 1])
        (list [rev tmp] xs) ;
      (let/ad xs
        [_ (cons a tmp) d (fx1- m)] ;consp
  ) ) )
  (_ nil xs m)
)

(def (head-tail xs m)
  (list (head xs m) (tail xs m))
)

(def cdr-nilp [lam (x) (nilp (cdr x))]) ;fz
(def car-nilp [lam (x) (nilp (car x))])

(def/va (same xs ys [= eql]) ;they are unique
  (def (~ ret xs)
    (if (nilp xs) ret
      (let/ad xs ;([ay(car ys)][dy(cdr ys)])
        (if [mem?% a ys =] ;=
          (~ (cons a ret) d)
          (~ ret d)
  ) ) ) )
  (~ nil xs) ;rev
)

(def/va (key->kv xz x [= eql] [defa? F] [defa nil]) ;
  (def (_ xz)
    (if (nilp xz)
      [if defa? defa x]
      (let ([kv (car xz)] [yz (cdr xz)])
        (if [= x (car kv)] ;
          kv ;
          [_ yz]
  ) ) ) )
  (_ xz)
)

;(key->val '([a 1][b 2][c]) 'c)
(def/va (key->val xz x [= eql] [f-case id] [defa? F] [defa nil]) ;
  (def (_ xz)
    (if (nilp xz)
      (if defa? defa x)
      (let ([xs (car xz)] [yz (cdr xz)])
        (if [= (f-case x) (car xs)] ;src-case
          [if (cdr-nilp xs) nil (cadr xs)] ;
          [_ yz]
  ) ) ) )
  (_ xz)
)

;key->x 'v/kv/nth k kvs = defa? defa ~base
(def/va (key->nth k kvs [base 1] [= eql] [defa? F] [defa nil]) ;
  (def (_ xz i) ;
    (if (nilp xz)
      [if defa? defa k]
      (let ([kv (car xz)] [yz (cdr xz)])
        (if [= k (car kv)]
          i ;k v kv i
          [_ yz (1+ i)] ;
  ) ) ) )
  (_ kvs base)
)

;(val->key '([a 1][b 2][c]) '3)
(def/va (val->key xz x [= eql] [f-case id]) ;
  (def (_ xz)
    (if (nilp xz) x
      (let ([xs (car xz)] [yz (cdr xz)]) ;hlp _ ~
        (if (cdr-nilp xs) x ;
          (if [= (f-case x) (cadr xs)] ;
            (car xs) ;
            [_ yz]
  ) ) ) ) )
  (_ xz)
)

(def (keys->val kvs . ks) ;keys->val / dot
  (def (keys->val% kvs ks)
    (if [nilp ks] kvs ;
      (let/ad ks          
        (if (consp kvs)
          [keys->val% (key->val kvs a) d] ;
          nil
  ) ) ) )
  (keys->val% kvs ks) ;
)

(def (lisp x)                   ;@ how about list? and your old code
  (and [pair? x]
    (null? (cdr [last-pair x])) ;5x ;last-pair@, dont use list?/lisp
) )

(def (list/sep xs sep)
  (list/seps xs (list sep))
)

;(list/sep% '(1 2 3) '(4 5)) ~> '(1 4 5 2 4 5 3)
(def (list/seps xs seps) ;head? tail?
  (def (_ ret xs)
    (if [nilp xs] ret ;
      (let ([a (car xs)])
        [_ (cons a (append seps ret)) (cdr xs)] ;
  ) ) )
  (let ([rs (rev xs)])
    [_ [list (car rs)] (cdr rs)]
) )

;(rand-seq '(+ - * /))
(def (rand-seq xs)
  (sort [lam (x y) (eq [random 2] 0)] xs)
)

;(keys->vals '([a 1] [b 2] [c 3] [d 4]) '(c d a b)) ;-> '(3 4 1 2)
(def/va (keys->vals KVs Ks [= eql] [key-case id] [defa? F] [defa nil]) ;
  (let ([conv (lam (k) (if defa? defa k))]) ;
    (def (_ ret kvs ks)
      (if~ (nilp ks) ret
        (let ([k(car ks)][dks(cdr ks)])
          (if~ (nilp kvs)
            [_ (cons [conv k] ret) KVs dks] ;or defa
            (let ([kv(car kvs)][dkvs(cdr kvs)])
              (if~ [= (key-case k) (car kv)] ;src-case
                (if (cdr-nilp kv)
                  [_ (cons [conv  k] ret) KVs dks] ;
                  [_ (cons (cadr kv) ret) KVs dks] )
                [_ ret dkvs ks]
    ) ) ) ) ) )
    [rev (_ nil KVs Ks)]
) )


;(chg-val-by-key (animal) 'name "dog")
(def/va (chg-val-by-key kvs k v [= eql]) ;case?
  (def (_ ret xz)
    (if [nilp xz] kvs ;f
      (letn
        ( [kv (car xz)] [yz (cdr xz)]
          [a  (car kv)] )
        (if [= a k]
          (cons (list k v)
            (append [rev ret] yz) ) ;t
          [_ (cons kv ret) yz]
  ) ) ) )
  (_ nil kvs)
)

;(chg-vals-by-keys (animal) '([name "dog"][action bark]))
(def/va (chg-vals-by-keys kvs kvs-new [= eql]) ;
  (def (_ xz yz)
    (if [nilp yz] xz
      (letn
        ( [a (car yz)] [d (cdr yz)]
          [k (car  a)] [v (cadr a)] )
        [_ (chg-val-by-key xz k v =) d] ;
  ) ) )
  [_ kvs kvs-new]
)

;'(lam xs (list xs))
;'(lam (x . xs) (list x xs))
;'(lam (x) (lam (x) (list x)))
;(lam-unify '(lam (x y) (list x y))) ;-> '(lam (x1 x2) (list x1 x2))
(def (lam-unify lam-expr)
  (letn
    ( [paras (No2 lam-expr)]
      [tmp  (list/-nth paras)]
      [mapp (map (lam (x) [list (car x) (str->sym (str 'x (cadr x)))]) tmp)] )
    (dmap (curry key->val mapp) lam-expr)
) )

(def/va (rotate! xs [n 1]) ;ret?
  (for [n] (car->end! xs)) ;@? [rev? F] ;end->car!
  xs ;?
)

;(list/swap-each2 '(2 1 4 3 5)) ;-> (range 1 5)
(def (list/swap-each2 xs) ;
  (def (~ ret xs)
    (if~
      [nilp xs] (rev ret)
      [nilp (cdr xs)] (append/rev-head ret xs) ;
      (let/ad xs
        [~ (cons* a (cadr xs) ret) (cddr xs)]
  ) ) )
  (~ nil xs)
)

; [duplicates '(123 321 123 321 321 1 2 3)] -> '(123 321 321 ...) -> remov-same
(def (duplicates xs)
  (def (_ xs sml ret)
    (if (nilp xs) ret
      (let ([a (car xs)] [d (cdr xs)])
        (if (mem? a sml)
          [_ d sml (cons a ret)]
          [_ d (cons a sml) ret]
  ) ) ) )
  ;[remov-same
    (_ xs nil nil)
  ;]
)

(def/va (next-to x xs [eq eq])
  (def (~ xs flg)
    (if~
      (nilp xs) nil
      flg
        (car xs)
      (eq x (car xs))
        (~ (cdr xs) T)
      (~ (cdr xs) flg)
  ) )
  (~ xs F)
)

(def [do-for xs f-xs f-xs-ret]
  (f-xs-ret xs [f-xs xs]) ;g f1 f2
)

(def (fill-rhs-nx xs n x)
  (append xs (xn->list x n))
)

(def (fill-lhs-nx xs n x)
  (append (nx->list n x) xs)
)

(def (fill-rhs xs x n)
  (letn
    ( [ln (len xs)]
      [m  (- n ln)] )
    (if (> m 0)
      (fill-rhs-nx xs m x)
      xs
) ) )

(def (fill-lhs xs x n)
  (letn
    ( [ln (len xs)]
      [m  (- n ln)] )
    (if (> m 0)
      (fill-lhs-nx xs m x)
      xs
) ) )

;(-% 'x 'y '(a y s x z))
;(-% 3 1 '(1 2 3 4)) ;1 nex nex -> 3 ;distance
(def (-% x y zs)
  (def (~ zs flg i f) ;
    (if [nilp zs] (f i)
      (let/ad zs
        (if~
          [eq y a]
            (if flg (f i) ;
              [~ d T i 1+] )
          [eq x a]
            (if flg (f i) ;
              [~ d T i 1-] )
          [~ d flg (f i) f]
  ) ) ) )
  (if [eq x y] 0
    [~ zs F 0 id]
) )

;cmp% x y zs -> '< > =
;(cmp% 'x 'y '(a y s d x z)) ;-> '< > =
(def/va (cmp% x y zs [ret-eq '=]) ;neq%
  (def (~ zs) ;
    (if [nilp zs] nil
      (let/ad zs
        (if~
          [eq x a] '<
          [eq y a] '>
          [~ d]
  ) ) ) )
  (if [eq x y] ret-eq
    [~ zs] ;
) )

;(close-to 3 '(1 2 4 5) '[1 2 3 4 5]) ;-> 2
;(close-to 'x '(a b y z) '(v a b x y z o)) ;-> 'b
(def/va (close-to% x ys zs [sorted? F] [fyx/z -%] [mk-lt/z (lam(zs) (lam(x y) (eq (cmp% x y zs) '<)))]) ;half?
  (let ([ys (if sorted? ys (qsort ys [mk-lt/z zs]))]) ;
    (def (~ ys las dis)
      (if (nilp ys) las
        (let/ad* ys
          ([new-dis (fyx/z a x zs)])
          (if (>= new-dis 0)
            (if [redu < (map abs (list new-dis dis))] ;
              a las )
            [~ d a new-dis]
    ) ) ) )
    (~ (cdr ys) (car ys) [fyx/z (car ys) x zs]) ;
) )

(def find-x-match
  (case-lam
    ([maker test cnt n0 nT] ;[sec 2]
      (def (_ ret n c)
        (if (> c cnt) ret
          (if (> n nT) ret ;
            (let ([x (maker n)])
              (if (test x)
                [_ (cons x ret) (1+ n) (1+ c)] ;
                [_ ret (1+ n) c]
      ) ) ) ) )
      (_ nil n0 1))
    ([maker test cnt n0](find-x-match maker test cnt n0 10000)) ;
    ([maker test cnt]   (find-x-match maker test cnt 0))        ;
    ([maker test]       (find-x-match maker test 1   0  10000))
) )

(def (flat-list-include ys0 xs0)
  (def (_ ys xs)
    (if (nilp xs) T
      (if (nilp ys) F
        (let ([dy (cdr ys)])
          (if [eq (car xs) (car ys)]
            [_ dy (cdr xs)]
            [_ dy xs0]
  ) ) ) ) )
  (_ ys0 xs0)
)
;(flat-list-include '(1 2 3 4 5) '(2 3))

(defn/defa assoc-g (x ys g) [id]
;(def (assoc-g x ys g)
  (let ([= (eq/eql x)])
    (def (_ ys)
      (if (nilp ys) nil ;
        (if [= (caar ys) x]
          (g (car ys))
          [_ (cdr ys)]
    ) ) )
    (_ ys)
) )

(def (w* num) (* num 10000))

(def [~remov-same xs] ;@
  (def (_ xs ts)
    (if (nilp xs) ts
      (let/ad xs
        (if (mem? a ts) ;
          [_ d ts]
          [_ d (cons a ts)] ;
  ) ) ) )
  [_ xs nil]
)

(def remov-1?
  (case-lam
    ([x xs eql] ;
      ;(def (remov-1?/g x xs g) ;result / #f
      (call/cc (lam [k]
          (def (_ xs)
            (if (nilp xs) [k F]
              (let ([a(car xs)] [d(cdr xs)])
                (if (eql a x) d
                  (cons a [_ d])
          ) ) ) )
          (_ xs)
    ) ) )
    ([x xs] (remov-1? x xs eql)) ;
) )
;(ali remov-1)

(def (list-and xs ys) ;common
  (def (_ xs ys ret)
    (if~
      (nilp ys) ret
      (letn ([y(car ys)] [dy(cdr ys)] [rmp(remov-1? y xs)]) ;
        (if rmp
          [_ rmp dy (cons y ret)]
          [_ xs dy ret]
  ) ) ) )
  (_ xs ys nil)
)

(def/va (tail% xs m [tail? F])
  (def (_ xs m)
    (if~
      (nilp xs) nil
      (< m 1) xs
      [_ (cdr xs) (1- m)]
  ) )
  (if tail?
    (_ xs (- (len xs) m))
    (_ xs m)
) )

(def (head% xs m)
  (def (_ xs n)
    (if~
      [nilp xs] nil
      [< n 1] nil
      (cons
        (car xs)
        [_ (cdr xs) (1- n)]
  ) ) )
  (_ xs m)
)

(def (zip . xz) ;(_ '(1 2) '(2 3) '(3 4 5)) ~> '((1 2 3) (2 3 4))
  (def (_ xz ret)
    (if [nilp (car xz)] ret
      [_ (map cdr xz) (cons (map car xz) ret)]
  ) )
  (if (nilp xz) nil
    [rev (_ xz nil)]
) )

;(trim-head '(1 1 2 1 1 2 1 1 3) '(1 1 2)) ;~> '(1 1 3)
(def (trim-head XS TS) ;n-times
  (def (_ ys ts)
    (if~
      (nilp ts)
        [trim-head ys TS] ;
      (nilp ys)
        XS
      (eq [car ys] [car ts])
        [_ (cdr ys) (cdr ts)]
      XS ;
  ) )
  (_ XS TS)
)

;(trim-tail '(1 4 3 2 3 2 3) '(2 3)) ;~> '(1 4 3)
(def (trim-tail xs ts) ;@
  (let
    ( [rxs (rev xs)]
      [rts (rev ts)] )
    [rev (trim-head rxs rts)] ;
) )

;(_ '(1 2 1 2 3 4 5 1 2 6 1 2 1 7 1 2 1 2) '(1 2)) ;~> '(3 4 5 6 1 7)
(def (trim-all XS TS) ;
  (def (_ ret tmp xs ts)
    (if (nilp ts)
      [_ ret nil xs TS] ;
      (let ([ta (car ts)] [td (cdr ts)]) ;
        (if (nilp xs)
          (append tmp ret) ;
          (let/ad xs
            (if (eq a ta)
              [_ ret (cons a tmp) d td]
              [_ (cons a (append tmp ret)) nil d TS] ;
  ) ) ) ) ) )
  [rev (_ nil nil XS TS)] ;
)

;(trim '(1 2 3 4 1 2) '(1 2)) ;~> '(3 4)
(def (trim-left xs ts)
  (trim-tail (trim-head xs ts) ts) ;
)
(def (trim-right xs ts) ;@
  (trim-head (trim-tail xs ts) ts)
)

;

(def/va (trim-head-1/flg xs serial [handled? F]) ;%flag ?
  (def (_ ys ts flg)
    (if~
      (nilp ts)
        [trim-head-1/flg ys serial T]
      (nilp ys)
        [list xs flg]
      (eq [car ys] [car ts])
        [_ (cdr ys) (cdr ts) flg] ;
      else (list xs flg)
  ) )
  (_ xs serial handled?)
)

;todo (trim-head-n '(1 2 3 4 1 2 5) '([1 2][3 4]) F)
(def/va (trim-head-n xs trims [handled? F]) ;once?
  (def (_ xs.flg ts)
    (let ([xs (car xs.flg)] [flg (cadr xs.flg)])
      (if (nilp ts)
        (if flg
          [trim-head-n xs trims F] ;
          xs )
        [_ (trim-head-1/flg xs (car ts) flg) (cdr ts)] ;
  ) ) )
  (_ (list xs handled?) trims)
)
;(trim-tail-n '(5 1 2 3 4 1 2) '([1 2][3 4])) ~> '(5)
(def/va (trim-tail-n xs trims [once? F])
  (let
    ( [rxs (rev xs)]
      [rts (map rev trims)] )
    [rev (trim-head-n rxs rts once?)]
) )

(def (trim-left-n xs trims)
  (trim-tail-n (trim-head-n xs trims) trims)
)
(def (trim-right-n xs ts)
  (trim-head-n (trim-tail-n xs ts) ts)
)

;(flow sym->str str-downcase str->sym)
(def (flow . fs)
  (flow% fs) ;
)
(def (flow% fs) ;
  (def (~ ret fs)
    (if [nilp fs] ret ;
      (~
        (lam (x) [(car fs) (ret x)]) ;
        (cdr fs)
  ) ) )
  (if [nilp fs] id
    [~ (lam xs [redu (car fs) xs]) (cdr fs)] ;
) )
(def (flow%1 fs) ;xs->x x->x ;map
  (def (~ ret fs)
    (if [nilp fs] ret ;
      (~
        (lam (x) [(car fs) (ret x)]) ;. (x)->xs ;redu
        (cdr fs)
  ) ) )
  (~ id fs) ;
)

(def/va (~do-for-pairs xs [f list])
  (def (_ ret xs)
    (if (cdr-nilp xs) ret
      (let/ad* xs ([ad (cadr xs)])
        [_ (cons (f a ad) ret) d]
  ) ) )
  (_ nil xs)
)

(def/va (do-for-pairs xs [f list])
  (def (_ xs)
    (if (cdr-nilp xs) nil
      (let/ad* xs ([ad (cadr xs)])
        (cons (f a ad) [_ d])
  ) ) )
  (_ xs)
)

(def/va (~odds xs [odd? T]) ;
  (def (_ ret xs odd?)
    (if (nilp xs) ret
      (let/ad xs
        (if odd?
          [_ (cons a ret) d F]
          [_ ret d T]
  ) ) ) )
  (_ nil xs odd?) ;
)

(def/va (odds xs [odd? T]) ;
  (def (_ xs odd?)
    (if (nilp xs) nil
      (let/ad xs
        (if odd?
          (cons a [_ d F])
          [_ d T]
  ) ) ) )
  (_ xs odd?) ;
)

;

(def/va (list/nth- xs [n0 1]) ;list->nth~ xs
  (def [_ xs n]
    (if (nilp xs) nil
      (cons
        (list n (car xs))
        [_ (cdr xs) (1+ n)] ;
  ) ) )
  [_ xs n0] ;
)
(def (list/-nth xs) ;list->nth~ xs
  (def (_ xs n)
    (if (nilp xs) nil
      (cons
        (li (car xs) n)
        [_ (cdr xs) (fx1+ n)]
  ) ) )
  (_ xs 1)
)

(def/va (list- xs ys [= nil]) ;@
  (def (_ xs ys)
    (if~
      (nilp xs) nil
      (nilp ys) xs
      [_ (remov-1 (car ys) xs =) (cdr ys)] ;
  ) )
  (_ xs ys)
)

(def (len-cmp f . xs) [redu f (map len xs)]) ;redu? len*?

(def (most% g xs . yz) ;(most (lam(l r)(?(> l r)l r)) 1 2 3)
  (def (_ xs yz)
    (if (nilp yz) xs
      (_ [g xs (car yz)] (cdr yz))
  ) )
  (_ xs yz)
)
(def (most g xz) ;(most (lam(l r)(?(> l r)l r)) '(1 2 3))
  (def (_ xs yz)
    (cond [(nilp yz) xs] ;faiz chk last time
      [else
        (_ [g xs (car yz)] (cdr yz)) ]
  ) )
  (_ (car xz) (cdr xz))
)

(def (longest . xz) ;(longest '(1 2) '() '(2 3)) ~> '(2 3)?
  (most
    [lam (l r)
      (if [len-cmp > l r] l r) ]
    xz
) )

(defn r-merge (xs ys) ;%
  (let ([m (len xs)] [n (len ys)])
    (if [>= m n] (ncdr xs [- n m])
      (append xs (ncdr ys m))
) ) )
(def l-merge (swap-para r-merge))

;

(def (ref% xs is . paras) ;xth% ;nth% array pont [offs 0]
  (def (_ xs is)
    (if (nilp is) xs
      (let/ad is
        [_ (ref xs a) d] ;
  ) ) )
  (_ xs is)
)

;[f ref]
(def/va (ref* xs ref [base 0] [defa nil] [pt-form? F] [conv id]) ;xth/head-tail -> '(a head tail)? [pt-form? F]
  (def (~ xs i) ;ref*/base
    (if~
      [consp xs]
        (let/ad xs
          (if (fx> base i) a ;30ms (li a [rev ~head] d) ;
            [~ d (fx1- i)] ;(cons a ~head)
        ) )
      defa
  ) )
  (def (_ xs ref)
    (if (nilp ref) [conv xs]
      (let/ad ref ;
        [_ (~ xs a) d]
  ) ) )
  (_ xs [if pt-form? (rev ref) ref])
)

(def/va (refs* xs rfz [f ref*]) ;
  (def (_ nz)
    (if (nilp nz) nil
      (let/ad nz
        (cons [f xs a] (_ d)) ;
  ) ) )
  (_ rfz)
)

;(chg-xth '((1)2) 0 3)
(def/va (chg-nth XS i [new nil] [base 1]) ;chg-nth-val [base 0] ;chg-val-by-a-ref
  (def (~ xs i)
    (if (nilp xs) nil ;
      (let/ad xs
        (if (<= i base)
          (cons new d) ;
          (cons a [~ d (1- i)])
  ) ) ) )
  (~ XS i)
)

;(setq asd '([1 (2 3)][4 5])) (chg-nth% asd '(1 2 2) 7)
(def/va (chg-nth% XS iths [new nil] [base 1]) ;chg-nth-val [base 0] ;chg-val-by-a-ref
  (def (~2 xs i iths)    
    (if (nilp xs) nil ;
      (let/ad xs
        (if (<= i base)
          (if [nilp iths] (cons new d)
            (cons [~ a iths] d) )
          (cons a [~2 d (1- i) iths])
  ) ) ) )
  (def (~ xs iths)
    (if (nilp iths) xs ;
      (let/ad iths
        (~2 xs a d)
  ) ) )
  (~ XS iths)
)

(def (chg-nth2 xs n . ys) ;
  [def (_ xs n ys)
    (if (nilp xs) xs
      (cond
        [(< n 1) (_ xs (fx1+ n) (cdr ys))]
        [(eq n 1) (r-merge ys xs)]
        [else
          (cons (car xs) [_ (cdr xs) (1- n) ys])
  ] ) ) ]
  (_ xs n ys)
)

;chg-nths, xs nths, y; .., n; cond case1 case2; init;
(def (chg-nths xs nths y) ; nths is sorted and uniqueness
  (def (_ xs nths n)
    (if~
      (nilp xs) nil
      (nilp nths) xs
      [eq (car nths) n]
        (cons y
          [_ (cdr xs) (cdr nths) (fx1+ n)] )
      (cons (car xs)
        [_ (cdr xs) nths (fx1+ n)]
  ) ) )
  (_ xs nths 1)
)

;(chg-pt-val '((1)2) '(0 0) 3)
(def/va (chg-ref-val xs ref [new nil] [base 0] [pt-form? F]) ;chg-val-by-ref [base 0] [pt-form? F]
  (def (chg~ xs ref i)
    (if~
      [nilp ref] ;full 3
        (chg-nth xs i new base)
      [nilp xs] ;end 4
        nil
      (let/ad xs
        (if
          [<= i base] ;nor-succ 1 => upd tmp?
            (cons [chg~ a (cdr ref) (car ref)] d)
          (cons a [chg~ d ref (1- i)]) ;nor 2 => 1-
  ) ) ) )
  (chg~ xs (cdr ref) (car ref))
)

;(replace2 '(a a a s) '(a a s) '(q w))
(def (list-repl xs Src Des) ;Des
  (let ([Des (rev Des)])
    (def (_ ret tmp xs src) ;ret tmp
      (if (nilp xs) ;
        (if (nilp src)
          (append Des ret)
          (append tmp ret) )
        (if (nilp src)
          [_ (append Des ret) nil xs Src] ;
          (let/ad xs
            (if (eq a [car src]) ;= eq
              [_ ret (cons a tmp) d [cdr src]]
              (if (nilp tmp)
                [_ (cons a ret) nil d src] ;
                (letn ([rtmp (rev tmp)] [a-rtmp (car rtmp)] [d-rtmp (cdr rtmp)])
                  [_ (cons a-rtmp ret) nil (append d-rtmp xs) Src] ;aaas aas ;(a 3)(s 1) (a 2)(s 1) ;@
    ) ) ) ) ) ) )
    [rev (_ nil nil xs Src)]
) )

;(replace '(#\a #\~ #\d #\x) '(#\~ #\d) '(#\1 #\2 #\3) 1)
;test and wrong: (replace '(a a a s) '(a a s) '())
(def/va (list-repl0 ls ORI NEW [times -1] [= eq]) ;
  (def (_ ls tmp xs n out-of-match?) ;
    (if~
      (nilp xs)   ;fully matched
        (append NEW [_ ls nil ORI (1- n) T])
      (nilp ls)
        (rev tmp) ;
      (eq n 0) ls ;
      (let ([a (car ls)] [d (cdr ls)])
        (if (= a (car xs))
          (if out-of-match?
            (append/rev-head tmp
              [_ d (list a) (cdr xs) n F] ) ;match starts
            [_ d (cons a tmp) (cdr xs) n F] )   ;matching
          (if out-of-match?
            [_ d (cons a tmp) xs n out-of-match?] ;nothing matches
            (append/rev-head tmp            ;ends the partly match
              [_ ls nil ORI n T]
  ) ) ) ) ) )
  (_ ls nil ORI times T)
)

;(~ xs '([t1 ..][t2 ..]) '(ys ..))

;(replace% '(z a b a d a b c a c b c) '([a b][a c][b c]) '(Y Z) T) ;-> '(z Y Z a d Y Z c Y Z Y Z)
;(replace% '(z a b a d a b c a c b c) '([a b][a c][b c]) '() F) ;-> '((6 2) (9) (11))
(def/va (replace% xs TZ [ys nil] [repl? T] [n -1]) ;
  (def (repl~ tmp ts xs tz n)
    (if~
      [eq 0 n] ;
        (append tmp xs)
      [nilp ts] ;~ eql
        (append ys
          [repl~ nil (car TZ) xs (cdr TZ) (1- n)] )
      [nilp xs] ;ret
        tmp
      (let/ad xs
        (if~
          [eq a (car ts)] ;eq
            [repl~ (cons a tmp) (cdr ts) d tz n]
          [nilp tz] ;~ !eql
            (cons a
              (append tmp [repl~ nil (car TZ) d (cdr TZ) n]) )
          (let ([tza (car tz)] [tzd (cdr tz)])
            [repl~ nil tza (append tmp xs) tzd n] ;!eq
  ) ) ) ) )
  (def (find~ ret tmi tmp ts i-ts xs tz n i j)
    (if~
      [eq 0 n]
        ret ;5
      [nilp ts] ;~ eql
        (find~
          (do-for ret (lam (xs) [cons tmi (nth xs i-ts)])
            (lam (xs x) (chg-nth xs i-ts x)) )
          nil nil (car TZ) 1 xs (cdr TZ) (1- n) (+ i j) 0 ) ;3
      [nilp xs]
        ret ;6
      (let/ad xs
        (if~
          [eq a (car ts)] ;eq
            (if (nilp tmp)
              [find~ ret  i (cons a tmp) (cdr ts) i-ts d tz n i (1+ j)] ;2
              [find~ ret tmi (cons a tmp) (cdr ts) i-ts d tz n i (1+ j)] )
          [nilp tz] ;~ !eql
            [find~ ret nil nil (car TZ) 1 d (cdr TZ) n (1+ i) 0] ;4
          (let ([tza (car tz)] [tzd (cdr tz)]) ;!eq
            [find~ ret nil nil tza (1+ i-ts) (append tmp xs) tzd n i 0] ;1
  ) ) ) ) )
  (if repl?
    [repl~ nil (car TZ) xs (cdr TZ) n]
    [find~ (xn->list nil (len TZ)) nil nil (car TZ) 1 xs (cdr TZ) n 1 0]
) )

;(replaces '(z a b a d a b c a c b c) '([a b][a c][b c]) '([X][Y Z][])) ;~> '(z X a d X c Y Z)
;do (_ xs '([(a s)(s d)][(d f)]) '([Z X][]) )
(def (replaces xs TZ YZ) ;
  (def (~ tmp ts  xs tz  yz)
    (if~
      [nilp ts] ;~ eql
        (append (car yz)
          [~ nil (car TZ) xs (cdr TZ) YZ] ) ;
      [nilp xs] ;ret
        tmp
      (let/ad xs
        (if~
          [eq a (car ts)] ;eq
            (~ (cons a tmp) (cdr ts) d tz yz)
          [nilp tz]       ;~ !eql
            (cons a
              (append tmp [~ nil (car TZ) d (cdr TZ) YZ]) ) ;
          (let ([tza (car tz)] [tzd (cdr tz)] [yzd (cdr yz)])
            (~ nil tza (append tmp xs) tzd yzd) ;!eq
  ) ) ) ) )
  (~ nil (car TZ) xs (cdr TZ) YZ) ;
)

;(exist? '(y a a a s x) '(a a s))
(def (exist? xs TS)
  (def (_ tmp xs ts)
    (if (nilp xs) F
      (if (nilp ts) T
        (let/ad xs
          (if (eq a [car ts]) ;= eq
            [_ (cons a tmp) d [cdr ts]]
            (if (nilp tmp)
              [_ nil d ts] ;
              [_ nil (append [cdr (rev tmp)] xs) TS] ;aaas aas ;(a 3)(s 1) (a 2)(s 1) ;@
  ) ) ) ) ) )
  (_ nil xs TS)
)

(def (divides xs seps)
  (def (~ xz seps)
    (if (nilp seps) xz
      (~
        (redu append
          (map [rcurry divide (car seps)] xz) ) ;
        (cdr seps)
  ) ) )
  [~ (list xs) seps]
)

;(separa '(x y z) 'e) ;-> '(x e y e z)
(def (separa xs sp)
  (def (_ xs)
    (if [nilp xs] nil
      (let/ad xs
        (cons* sp a [_ d]) ;
  ) ) )
  (if (nilp xs) nil
    (let/ad xs
      (cons a [_ d])
) ) )

;(count [str->list "xs"] [str->list "lkjxslkxjslkxslkxjslk"])
(def (count YS xs)
  (def (~ xs ys i)
    (if [nilp xs] i
      (let/ad xs
        (if [nilp ys]
          (~ xs YS (1+ i))
          (let ([ay (car ys)] [dy (cdr ys)])
            (if [eq a ay]
              (~ d dy i)
              (~ d YS i)
  ) ) ) ) ) )
  (~ xs YS 0)
)

; todo: 1层压缩 -> 全压缩
(def/va (compress% x n xs [= eq])
  (def (_ xs x n)
    (if (nilp xs)
      (list [list x n]) ;
      (let/ad xs
        (if (= x a) ;
          [_ d x (1+ n)]
          (cons [list x n] [_ d a 1])
  ) ) ) )
  (_ xs x n)
)
(def/va (compress xs [= eq]) ;
  (if (nilp xs) nil
    (compress% (car xs) 1 (cdr xs) =)
) )
;test: '(1 2 3 1 2 3 4)
;weak when '(1 3 4 6 2) ;all diffe

;(_ '(1 2 1 2 3 0 1 2 3)) ;-> 1 2 3 -> '(([1 2 3] 2) ([1 2] 1) ([0] 1))

(def/va (decompress xz [append? T]) ;
  (let
    ( (tmp
        (map (lam (xs) (nx->list (cadr xs) (car xs))) xz)
    ) )
    (if append? (redu append tmp) tmp)
) )

;elap cant print ""

(def (logic-and . bs) ;&&
  (def (~ bs)
    (if (nilp bs) T
      (let/ad bs
        (if~ a
          [~ d]
          F
  ) ) ) )
  (~ bs)
)
(def (logic-or . bs) ;f-or
  (def (~ bs)
    (if (nilp bs) F
      (let/ad bs
        (if~ a T
          [~ d]
  ) ) ) )
  (~ bs)
)

; number

(def (half x)
  (/ x 2)
)

(def (int n) ;[exa? F]
  (def (_ n)
    (if (number? n)
      (if~
        [inexact? n] (inexact->exact (round n)) ;@ ?float->fix
        [int? n]     n
        [_ (inexa n)] )
      n ;
  ) )
  (_ n)
)

;num<->char num/char
(def (digit->char x)
  (int->char [+ (char->int #\0) x])
)

(def (char->digit x)
  (redu - [map char->int (list x #\0)])
)

;(num->int/system num 36~62) ;numeration/num<->str
(def/va (int->str/system num [scale 10] [chars (append *chs-numbers* *chs-Letters*)]) ;'(0 1 .. A .. Z)
  (def (_ ret num)
    (if [<= num 0] ret ;eq
      (let
        ( [rem (% num scale)]
          [quot (quotient num scale)] )
        [_ (cons rem ret) quot]
  ) ) )
  (list->str [map (curry xth chars) (_ nil [int num])]) ;
)

(def/va (str->int/system snum [scale 10] [chars (append *chs-numbers* *chs-Letters*)]) ;snum ;case?
  (def (_ ret xs) ;
    (if [nilp xs] ret
      (let/ad xs
        [_ (+ (* ret scale) a) d]
  ) ) )
  (_ 0 (map [flow (rcurry nth-of chars) fx1-] [str->list snum])) ;
)

(def/va (int->list num [scale 10] [Syms (append *syms-numbers* *syms-Letters*)]) ;'(0 1 .. A .. Z)
  (def (_ ret num)
    (if [eq 0 num] ret
      (let
        ( [rem (% num scale)]
          [quot (quotient num scale)] )
        [_ (cons rem ret) quot]
  ) ) )
  [map (curry xth Syms) (_ nil num)] ;
)
;(int->list/scale 123 10) -> '(1 2 3)
(def/va (int->list/scale num [scale 10])
  (def (_ ret num)
    (if [= 0 num] ret ;
      (let
        ( [rem (% num scale)] ;
          [quot (quotient num scale)] )
        [_ (cons rem ret) quot]
  ) ) )
  (_ nil num)
)

(def/va (list->int/scale xs [scale 10]) ;tab
  (def (_ ret xs)
    (if [nilp xs] ret
      [_ (+ (* ret scale) [car xs]) (cdr xs)] ;
  ) )
  (_ 0 xs)
)

(def (num->nums/carry num cs) ;left-align
  (def (~ ret num cs)
    (if (nilp cs) ret ;
      (let/ad* cs
        ( [x (% num a)] ;
          [rest (quotient num a)] )
        [~ (cons x ret) rest d]
  ) ) )
  (~ nil num [rev cs])
)
(def (nums->num/carry xs cs) ;[base 0] ;- x base
  (def (~ ret xs cs)
    (if [nilp xs] ret
      (if [nilp cs] (cons ret xs) ;
        [~ (+ (* ret [car cs]) [car xs]) (cdr xs) (cdr cs)]
  ) ) )
  (~ 0 xs cs)
)

;(fmt-nums/carry '(23 23 123) '(24 60 60)) ;xs~>z->ys
(def (fmt-nums/carry xs form) ;.%? ;fmt-1st?
  (def (~ ret xs ys carry)
    (if (nilp xs) ret
      (if (nilp ys) (append xs ret)
        (letn
          ( [a (car xs)] [d (cdr xs)]
            [ay(car ys)] [dy(cdr ys)]
            [new-x (+ carry a)]
            [new-carry (int/ new-x ay)] ;
            [rest (% new-x ay)] )
          (~ (cons rest ret) d dy new-carry)
  ) ) ) )
  (let ([len-ys (len form)])
    (append (~ nil (rev [head% xs len-ys]) (rev [head% form (len xs)]) 0) [tail% xs len-ys])
) )
;number

; string

;(str-repl% "adssadas.ds.ad" '("ad" "s.") "X")
(def/va (str-repl% s0 sz [s2 ""] [n -1] [repl? T])
  (letn
    ( [conv str->list] [deconv list->str]
      [tmp (replace% [conv s0] [map conv sz] [conv s2] repl? n)] ) ;
    (if repl?
      (deconv tmp)
      tmp
) ) )

(def/va (str-repl ss sx sy [num -1]) ;~ ;(redu str-repl% [map str->list (list ss sx sy)])
  (list->str
    (replace [str->list ss] [str->list sx] [str->list sy] num eq) ;
) )
; (def (str-repl% chs csx csy)
  ; (list->str (list-replace chs csx csy )) ;str is slow
; )
;(str-repls "asd.\nsdf.dfg" '["\n" "."] '["" " . "]) ;~> "asd . sdf . dfg"
(def/va (str-repls st ss ts) ;
  (let ([conv str->list] [deconv list->str])
    [deconv (redu (curry replaces [conv st]) [map (curry map conv) (list ss ts)])] ;
) )

(def (str-exist? ss st)
  [exist? (str->list ss) (str->list st)]
)

;(str-divides "a/s/d\\sadsd" '("/" "\\"))
(def (str-divides ss seps)
  [map list->str (divides (str->list ss) (map str->list seps))]
)

(def/va (str-trim-head ss [mark " "])
  (let ([conv str->list])
    (list->str [trim-head (conv ss) (conv mark)])
) )

(def (str-count s ss)
  (let ([conv str->list])
    (count [conv s] [conv ss])
) )

(def (hex dec)
  (if (num? dec)
    (dec->hex dec)
    dec
) )

(def/va (str-trim ss [s-trim " "]) ;_ "asasda" "as"
  (str [trim (str->list ss) (str->list s-trim)])
)
;(str-trim-all "asd.sda.sa." ".s")
(def/va (str-trim-all ss [s-trim " "])
  (str [trim-all (str->list ss) (str->list s-trim)])
)

;(str-trim-n "asdsadsads" '("as" "ds")) ;~> "adsa"
(def/va (str-trim-n ss [trims '(" ")])
  (str [trim-n (str->list ss) (map str->list trims)])
)

;(strcat/sep '("a" "sd" "fg") [" "])
(def/va (strcat/sep sz [sep " "])
  (def (_ ret xs)
    (if [nilp xs] ret
      (let/ad xs
        [_ (strcat ret sep a) d] ;
  ) ) )
  (if (nilp sz) ""
    [_ (car sz) (cdr sz)]
) )

;(str/sep-chars "asddsa")
(def/va (str/sep-chars ss [seps '(#\x0)]) ;[encry (rcurry str/sep-chars '(#\x0))]
  [list->str (list/seps (str->list ss) seps)] ;
)

;(strcat/sep-per (xn->list "asd" 10) "\n" 3)
(def (strcat/sep-per ss sep per)
  (def (_ ret xs i)
    (if [nilp xs] ret
      (let/ad xs
        (if (eq i per) ;
          [_ (strcat ret sep a) d 1]
          [_ (strcat ret a) d (1+ i)]
  ) ) ) )
  (if [nilp ss] ""
    [_ (car ss) (cdr ss) 1]
) )

; shell

(def (command-result cmd)
  (let-values
    ( ( [in ou er id]
        (open-process-ports cmd ;
          (buffer-mode block)
          (make-transcoder (utf-8-codec))
    ) ) )
    (let ~ ([ret nil])
      (if (eof-object? (peek-char ou))
        (str (rev ret)) ;\r\n
        [~ (cons (read-char ou) ret)] ;
) ) ) )


(def [bool x] (if x T F)) ;nil? 0? ;does it conflit with bool type in ffi ?

(def (bool->string b) (?: (fal? b) "#f" "#t"))

; (def (any->str/raw x)
  ; (cond
    ; ((symbol? x) (sym->str            x)) ;
    ; ((bool?   x) [if x "#t" "#f"]) ;               x
    ; ((number? x) (number->string      x))
    ; ((char?   x) (list->string (list  x)))
    ; ((string? x)                      x)
    ; ((list?   x) (lis->str            x))
    ; ((pair?   x) (lis->str(pair->list% x)))
    ; ((fn?     x)  "") ;ty?
    ; ((atom?   x) (sym->str           'x)) ;
    ; (els          "")
; ) )

(def (any->str x)
  (cond
    ((symbol? x) (sym->str            x)) ;
    ((bool?   x)                      "") ;               x
    ((number? x) (number->string      x))
    ((char?   x) (list->string (list x)))
    ((string? x)                       x)
    ((list?   x) (lis->str            x)) ;
    ((pair?   x) (lis->str (pair->list% x)))
    ;((ffi?   x) (sym->str           'x)) ;name?
    ((fn?     x)  "") ;ty?
    ((void?   x)  "")
    ((atom?   x) (sym->str           'x)) ;
    (else         "")
) )
(def (lis->str xs) ;
  (redu~ strcat (map any->str xs)) ;
) ;lis2str

(def (list->num xs) ;10 based
  (def (_ xs ret)
    (if (nilp xs) ret
      [_ (cdr xs) (+ (* ret 10) [car xs])]
  ) )
  (_ xs 0)
)

(def (str . xs) (lis->str xs))

(def (pair->list% pr) ;'(1 . ()) ~> '(1 ())
  (list (car pr) (cdr pr))
)

(def (xn-mk-list% xns)
  (def (_ x n ys)
    (if [> n 0]
      (cons x [_ x (1- n) ys]) ;
      (if (nilp ys) nil
        (if [nilp (cdr ys)]
          (list (car ys))
          [_ (car ys) (cadr ys) (cddr ys)]
  ) ) ) )
  (_ nil 0 xns)
)
(def (xn-mk-list . xns) (xn-mk-list% xns)) ;

(def/va (nx->list n x [xs0 nil]) ;a bit faster than make-list ; xs0
  (def (_ n ret)
    (cond
      [(< n 1) ret]
      [else
        (_ (1- n) [cons x ret]) ] ; cons is fast
  ) )
  (_ n xs0)
)

(defn nlist% (xs n) ;xs need append is slow
  (def [_ n ret]
    (if (< n 1) ret
      (_ (1- n) [append xs ret]) ;
  ) )
  (if (nilp xs) nil
    (_ n nil)
    ; (append% (xn2lis xs n))
) )

;ex

(def (ncdr xs n)
  (if~
    [< n 0]
     (head xs (+ (len xs) n)) ;@
    [> n 0]
     (tail% xs n) ;consider if outofrange
    xs
) )

; (def (ncdr% xs n)
  ; (if~
    ; [< n 0]
     ; (head xs (+ (len xs) n)) ;@
    ; [> n 0]
     ; (tail% xs n) ;inc out-of-range
    ; xs
; ) )

(def (call g . xs) (redu g xs)) ;
(def (rcall% g . xs) (redu g (rev xs)))

;eg doer: do-for xs car (lam(xs x)[cons [do-for x cadr (lam(xs x)[list (car xs) [fx+ x X]])] (cdr xs)])
;(member?%2 'x '(y x z))
(def/va (member?% X xs [= eql] [doer id] [full-info? F]) ;member (member? member?%) mem? mem?%
  (letn
    ( [ret0 (lam (v t) v)]
      [ret1 (lam (v t) [list v (rev t)])]
      [ret-er (if full-info? ret1 ret0)] ) ;
    (def (_ tmp xs) ;
      (if~
        [nilp xs]
          (ret-er F tmp) ;
        [= (car xs) X] ;
          (ret-er (doer xs) tmp) ;
        [_ (cons [car xs] tmp) (cdr xs)] ;collector @
    ) )
    (_ nil xs)
) )

(def (echo% sep . xs) ;(_ xs [sep " "]) ;voidp
  (def (_ sep xs)
    (case [len xs] ;
      ([0] (void))
      ([1] (disp (car xs))) ;
      (else
        (disp (car xs) sep)
        [_ sep (cdr xs)] ;
  ) ) )
  (if~ *will-disp*
    (_ sep xs)
) )
(def (echo . xs) (apply echo% (cons " " xs))) ;

;test (range 10 1)
(def myrange ;-> (0 ... n-1)
  (case-lam
    ( [s e] ;~
      (def (_ ret e)
        (if (< e s) ret ;
          [_ (cons e ret) (1- e)] ;
      ) )
      (_ nil e) )
    ( [n] ([if chez? #%iota range] n) ) ;
    ( [s e p] ;@
      (let ([g (if [>= p 0] > <)])
        (def (_ i)
          (if (g i e) nil
            (cons i [_ (+ i p)])
        ) )
        (cons s [_ (+ s p)]) ;
    ) )
    ( [s e f p] ;n ;0 1
      (let ([g (if (>= [f s p] s) > <)]) ;sign
        (def (_ i)
          (if (g i e) nil ;f ;range x m M ;min-max xs
            (cons i [_ (f i p)])
        ) )
        (cons s [_ (f s p)]) ;init
    ) )
    ( [total s f p e] ;
      (let ([g (if [>= (f s p) s] > <)]) ;
        (def (~ res x)
          (let ([res (- res x)])
            (if~ (or [< res 0] [g x e]) ;
              nil
              (cons x [~ res (f x p)]) ;cons
        ) ) )
        [~ total s]
    ) )
    ; ( [s e f p n] ;n e
      ; (let ([g (if [>= (f p) 0] > <)]) ;*|/
        ; (def (_ i)
          ; (if (g i e) nil
            ; (cons i [_ (f i p)]) ;
        ; ) )
        ; (cons s [_ (f s p)])
    ; )
) )

(def/va (~range x0 n [f (lam (x) (1+ x))]) ;~range x0 n f
  (def (~ ret tmp n)
    (if [eq n 0] ret ;
      (~ (cons tmp ret) (f tmp) (1- n)) ;
  ) )
  (~ nil x0 n) ;
)

;(range/total 30 4 ./ 2 0.1) ;
(def/va (~range/total total [s 0] [f +] [p 1] [e nil]) ;n ;range-n
  (def (_ ret res x) ;rest-->0
    (let ([res (- res x)])
      (if [< res 0] ret
        [_ (cons x ret) res (f x p)]
  ) ) )
  (if (nilp e)
    [_ nil total s]
    (let ([g (if [> (f s p) s] > <)]) ;
      (def (~ ret res x) ;x-->e
        (let ([res (- res x)])
          (if~
            [< res 0] ret
            [g x e] ret
            [~ (cons x ret) res (f x p)] ;
      ) ) )
      [~ nil total s]
) ) )

(def range/total ;total n s f p e
  (case-lam
    ( [total]
      (range/total total 0 + 1 total) )
    ( [total n]
      (range/total total n + 1) ) ;* 2
    ( [total f p] ;if f is -
      (let ([s 1])
        (def (~ res x)
          (let ([res (- res x)])
            (if [< res 0] nil
              (cons x [~ res (f x p)]) ;
        ) ) )
        [~ total s]
    ) )
    ( [total n f p] ;s/e
      (let ([s 1]) ;
        (def (~ ret res x i)
          (let ([res (- res x)])
            (if (or [eq n i] [< res 0])
              ret
              [~ (cons x ret) res (f x p) (fx1+ i)] ;
        ) ) )
        (letn
          ( (ret [~ nil total s 0])
            [s (./ total (redu + ret))] ) ;
          [~map1 (lam (x) (* x s)) ret] ;
    ) ) )
    ( [total n s f p] ;
      (let ([g (if [>= (f s p) s] > <)]) ;
        (def (~ res x i)
          (let ([res (- res x)])
            (if~ (or [eq n i] [< res 0]) ;
              nil
              (cons x [~ res (f x p) (fx1+ i)]) ;cons
        ) ) )
        [~ total s 0]
    ) )
    ( [total n s f p e]
      (let ([g (if [>= (f s p) s] > <)]) ;
        (def (~ res x i)
          (let ([res (- res x)])
            (if~ (or [eq i n] [< res 0] [> x e]) ;
              nil
              (cons x [~ res (f x p) (fx1+ i)]) ;
        ) ) )
        [~ total s 0]
    ) )
) )

(def (vec-range n)
  [def (_ n ret)
    (for (i n)
      (vector-set-fixnum! ret i i) )
    ret ]
  [_ n (make-vector n)]
)

;rpush 1 nil


(def (echol . xs)
  (apply echo xs) (newline) ;
)

(def [read-expr . xs]
  (let
    ( (p
        (open-input-string
          (redu~ strcat ;
            `["(begin " ,@xs ")"] ;
    ) ) ) ) ;ign spc between
    [read p]
) )

;'((^)(* / %)(+ -))
(defn read-math-expr xs
  (let
    ([p (open-input-string
          (redu~ strcat
            `("'(" ,@xs ")") ) ) ])
    (read p)
) )

(def (evs . xs) (ev [redu read-expr xs])) ;

(defn chars-replace-x (cs x xx)
  (defn _ (cs x xx ret)
    (if (nilp cs) ret
      (letn (
          [a (car cs)]
          [b (eq a x)] )
        (_ (cdr cs) x xx ([if b append conz] ret [if b xx a]))
  ) ) )
  (_ cs x xx nil)
)

; (defn string-replace (s a b) ;
  ; (list->string (chars-replace-x (string->list s) a (string->list b)))
; )

;'((1 * 2 + 3 * 4) - 5) =>
;(_ '((1 * 2 + 3 * 4) - 5)) => '(((1 * 2) + (3 * 4)) - 5)
;(defn f () nil)

(define (union x y)
  (if (pair? x)
    (if (memv (car x) y) ;
      (union (cdr x) y)
      (cons (car x) (union (cdr x) y)))
    y
) )

(define (every pred lst)
  (if (pair? lst)
    (if (pred (car lst))
      (every pred (cdr lst))
      #f)
    #t
) )

(define (some pred lst)
  (if (pair? lst)
    (or (pred (car lst))
      (some pred (cdr lst)))
    #f
) )

(def (getf* xs xtag) ;`(:n ,n :x ,x)
  (if (<(len xs)2) nil
    (if (eq (car xs) xtag)
      (cadr xs)
      [getf* (cddr xs) xtag]
) ) )

(def (get-as-arr xs . iz) ;[_ '((1 2)(3 4)) 0 0]
  (def (_ xs iz)
    (if (nilp iz) xs
      (if (consp xs)
        [_ (xth xs (car iz)) (cdr iz)] ;
        nil
  ) ) )
  (_ xs iz)
)

(def (char->string x) (list->string (list x)))

(def (str-explode s)
  (map char->string (string->list s))
)

;

(def/va (ref xs i [base 0]) ;10ms
  (def (~ xs i)
    (if ;10ms ;(nilp xs) xs
      [consp xs]
        (let/ad xs
          (if (<= i base) a ;30ms
            [~ d (1- i)]
        ) )
      xs ;10ms
  ) )
  (~ xs i)
)

; (def/va (ref% xs is [base 0]) ;xth% ;nth% array pont [offs 0]
  ; (def (_ xs is)
    ; (if (nilp is) xs
      ; (let/ad is
        ; [_ (ref xs [- a base]) d] ;
  ; ) ) )
  ; (_ xs is)
; )

(def/va (nth% xs ns [conv id]) ;[defa nil]
  (def (_ xs ns)
    (if (nilp ns)
      [conv xs] ;
      (let/ad ns
        [_ (ref xs [1- a]) d] ;.
  ) ) )
  (_ xs ns)
)

(def/va (xth% xs ns [conv id]) ;[defa nil]
  (def (_ xs ns)
    (if (nilp ns)
      [conv xs] ;
      (let/ad ns
        [_ (ref xs a) d] ;.
  ) ) )
  (_ xs ns)
)

(def (xth xs . is)
  (def (_ x is i) ;
    (if (nilp is)
      (list-ref x i)
      [_ (list-ref x i) (cdr is) (car is)] ;
  ) )
  (_ xs (cdr is) (car is)) ;
)
(def (nth xs . nths) ;45ms
  (def (_ x nths i) ;
    (if (nilp nths)
      (list-ref x i)
      [_ (list-ref x i) (cdr nths) (1- (car nths))] ;
  ) )
  [_ xs (cdr nths) (1- (car nths))] ;
)

;(~ '([(1 2)(3 4)][(5)(6)]) '([1 1 1][2 2 1])) ;-> '(1 6)
(def/va (refs xz rfz [f ref%]) ;
  (def (~ xs ns)
    [f xs ns] ) ;nth != pt
  (def (_ nz)
    (if (nilp nz) nil
      (let/ad nz
        (cons [~ xz a] (_ d)) ;
  ) ) )
  (_ rfz)
)

(def/va (pt->val xs pt [conv id]) ;offs-0?
  (nth% xs [rev pt] conv) ;
)
(def/va (pt->val/try xs pt [conv id] [defa nil]) ;offs-0?
  (let ([tmp [try (nth% xs [rev pt] conv)]])
    (if (try-fail? tmp) defa
      tmp
) ) )

(def (nths xs nz)
  (refs xs nz nth%)
)
(def/va (pts->vals xs pts [conv id])
  (refs xs pts (rcurry pt->val conv)) ;
)

(def [car-consp x] (consp (car x)))
(def [car-atomp x] (atomp (car x)))

;pieces of the most beautiful code

(def/doc (rev xs)
  (def (_ ret xs)
    (if (nilp xs) ret
      (_ [cons (car xs) ret]
        (cdr xs)
  ) ) )
  [_ nil xs]
)

(def/doc (flat xs)
  (def (_ ret x) ;
    (if~
      [nilp x]
        ret
      [consp x]
        (_ [_ ret (cdr x)] (car x))
      (cons x ret)
  ) )
  (_ nil xs)
)

(def/va (walk-lhs x [lhs? T] [doer id]) ;depth first search ;vs flat
  (def (_ ret x)
    (if~
      (nilp x) ret ;
      (consp x)
        (let/ad x
          (if lhs?
            (_ [_ ret a] d) ;~
            (_ [_ ret d] a) ;@
        ) )
      (cons [doer x] ret)
  ) )
  (_ nil x)
)

(def/doc (deep-length xs)
  (def (_ x n)
    (if~
      [nilp  x] n
      [consp x]
      (_ (car x)
        [_ (cdr x) n] )
      (fx1+ n) ;
  ) )
  (_ xs 0)
)
;(d-len '[((a b)c)(d e)]) ;-> 5

(def (flat-and-remov x xs)
  (let ([g (eq/eql x)])
    (def (_ xs ret)
      (cond
        [(nilp  xs) ret]
        [(g x xs)   ret] ;
        [(consp xs)
          (_ (car xs)
            (_ (cdr xs) ret) ) ]
        [else (cons xs ret)]
    ) )
    (_ xs nil)
) )

(def/doc (bump xs fmt) ;bumpl/bumpup-lhs
  (def (_ x fmt ret)
    (if~
      [nilp  fmt] ret
      [consp fmt]
        (letn ([fa (car fmt)] [fd (cdr fmt)] [ln (d-len fa)] [head. (head x ln)] [tail. (tail x ln)])
          (if (car-consp fmt)
            (cons [_ head. fa ret] [_ tail. fd ret]) ;cons _ _
            [_ (car x) fa [_ tail. fd ret]] ;car
        ) )
      (cons x ret)
  ) )
  (_ xs fmt nil)
)

;

(def (redu-map r m xs) (redu r (map m xs))) ;syn for such-as or

(def (tru? b)
  (if (eq #t b) #t #f)
)
(alias fal? not) ;
(def  (neq x y) [not(eq  x y)])
(defn !eql (x y) [not(eql x y)])

(def (tyeq x y) ;
  (eq (ty x) (ty y)) ;
)
(def (ty-neq x y)
  (neq (ty x) (ty y))
)

(def (sym< x y) (redu-map string<? sym->str (list x y)) )
(def (sym> x y) (redu-map string>? sym->str (list x y)) )

(def (atom-cmp x y)
  (letn
    ( [type (ty x)]
      (<>
        (case type
          ('string (list string<? string>?))
          ('char   (list char<? char>?))
          ('symbol [list sym< sym>])
          ('number (list < >))
          ;vector
          (else nil)
    ) ) )
    (if (eq type (ty y))
      (if (nilp <>)
        (if (eql x y) = nil) ;
        (cond
          ([(car  <>) x y] '<)
          ([(cadr <>) x y] '>)
          (else '=)
      ) )
      nil ;
) ) )
(def (mk<>= f xs cmp)
  (let ([resl (redu f xs)])
    (if (nilp resl) nil
      (eq resl cmp)
) ) )
(def (atom> x y) (mk<>= atom-cmp (list x y) '>))
(def (atom< x y) (mk<>= atom-cmp (list x y) '<))

(def (any-cmp xs ys)
  (def (_ xs ys)
    (if [nilp xs] '= ;
      (if [consp xs] ;? < atom nil pair list
        (let ([x (car xs)] [y (car ys)])
          (if [consp x]
            (let ((resl [_ x y]))
              (case resl
                (= [_ (cdr xs) (cdr ys)])
                (else resl)
            ) )
            (if [ty-neq x y] nil ;
              (let ([resl (atom-cmp x y)]) ;
                (case resl
                  (= [_ (cdr xs) (cdr ys)])
                  (else resl)
        ) ) ) ) )
        (atom-cmp xs ys)
  ) ) )
  (_ xs ys)
)
;(defn any> (x y) (mk<>= any-cmp (li x y) '>))
(def (any> x y) [eq (any-cmp x y) '>])
(def (any< x y) [eq (any-cmp x y) '<])
(def (any= x y) [eq (any-cmp x y) '=])

(def (assert0 resl test)
  (echol
    (if (eql resl test) 'Ok
      'Wrong!!
) ) )

; convert

(def (dec->hex dec) (fmt "0x~x" dec)) ;~2x
(def (hex->dec hex) (evs (str-repl hex "0" "#" 1))) ;@

; API

(def/va (sleep% [sec 0] [ms 0]) (#%sleep (make-time 'time-duration [fixnum (* ms (pow 10 6))] [fixnum sec])))

(def/va (sleep-ms [ms 0])
  (letn
    ( [ts  (fill-lhs (int->list/scale (int ms) 1000) 0 2)] ;
      [sec (car  ts)]
      [ms  (cadr ts)] )
    (sleep% sec ms)
) )
(def/va (sleep-sec [sec 0])
  (letn
    ( [ts  (fill-lhs (int->list/scale (int (* sec 1000)) 1000) 0 2)] ;
      [sec (car  ts)]
      [ms  (cadr ts)] )
    (sleep% sec ms)
) )

(def/va (retry f [times 1] [ms 1])
  (def (~ times)
    (if [<= times 0] F
      (if [f] T
        (bgn
          (sleep-ms ms)
          [~ (1- times)]
  ) ) ) )
  [~ times]
)

;(_ '([(1 2)(3 4)][(5 6)(7 8)])) ;-> '(r[r(1 2)r(3 4)]r[r(5 6)r(7 8)])
(def (flip xs)
  (map deep-rev xs)
)

(def (call-xn g x n)
  (redu g (xn->list x n))
)

; demo

(def/va (get-https-ret url [file (rand-filename 8 ".txt")])
  (let
    ( [ret nil] ;wget -q -O - {url}
      [cmd (str "wget -q --no-check-certificate -O " file " \"" url "\"")] ) ;no chk for ssl
    (sys cmd)
    (setq ret (read-file-0 file)) ;
    (delete-file file) ;
    ret
) )

;(cost (gotcha 24 '(1 2 5 10 nil) '(+ - * / eq id cons list) =))
;(cost (_ 24 '(1 2 3 4 nil + - * / cons eq list) '() =))
;(cost (_ (church 2) '(1) '(church church1+) church=))
;(cost (_ (church 2) '(1 church1) '(church church+) church=))
;car/cdr atomp, cons eq, If Quote
;todo: num-paras/layer fmt rand? glob?
;think: (), a, (f a b), (f a (g b c)), ...
;ret: (_ data ops n-data [pkrs])
;data-2: (choose [push data (_)]) ?push-diffe
(def/va
  (gotcha [tar 24] [data '(0. 1 2 3 4 5 6 7 8 9 nil T F)]
    [ops '(+ - * / eq cons)] [= =] [packers '(list rlist)] )
  [setq *paths* nil] ;clean-choose
  (letn ;
    ( [data (rand-seq data)] ;
      [a (choose data)]
      [b (choose data)]
      [c (choose data)] ;[ds (chooses data 3)] let-values

      [f (choose [if (nilp ops) data ops])] ;try rand ;n-ops = 1- n-data
      [g (choose [if (nilp ops) data ops])]

      [p1 (choose packers)] ;n-pkrs ;(+ 1(- 2(* 3 4))) / (+(- 1 2)(* 3 4)) ;?choose-again, recall gotcha

      [tmp `(redu ,f (,p1 ,a [redu ,g (list ,b ,c)]))] ;(+ 1 (* 2 3))
      [resl (try [= tar (ev tmp)])] ;
      [bool (if (try-fail? resl) F resl)] )
    (if bool
      (cons f ([ev p1] a (cons g (list b c)))) ;exp
      [fail] ;fail-and-goon
) ) )

(def/va (mem?-and-do x xs [= eql] [get id] [f-x id]) ;keep whole xs
  (def (_ ret xs)
    (if~
      [nilp xs] F
      (let/ad xs
        (if [= x [get a]]
          (append [rev ret] (cons [f-x a] d)) ;(cons [f-x a] d) ;
          (_ [cons a ret] d) ;(_ ret d) ;
  ) ) ) )
  (_ nil xs)
)

;(elem-freq% '(1 2 2 3 123 2 1 323 2 1 2))
(def/va (elem-freq% xs [= eq]) ;~
  (def (_ ens xs)
    (if [nilp xs] ens
      (let/ad xs ;mem?-and-do a xs eq car do
        (letn
          ( [do-sth (lam (xs) (do-for xs [lam(xs)(1+ (cadr xs))] [lam(xs x)(list (car xs) x)]))]
            [tmp (mem?-and-do a ens = car do-sth)] ) ;?
          (if tmp
            [_ tmp d]
            [_ (cons [list a 1] ens) d] ;rev
  ) ) ) ) )
  [_ nil xs]
)

(def (elem-freq xs)
  (qsort
    ;(compress (qsort xs any<))
    (elem-freq% xs eq)
    [lam (x y) (> (cadr x) (cadr y))]
) )

;(565->rgb (hex->dec "0xe7c1")) ;-> '(r g b) ;c1e7?
(def (565->rgb iCol) ;5 6 5->8 8 8
  (letn
    ( [arb (arb-group [fill-lhs (str->list (int->str/system iCol 2)) #\0 16] 5 6 5)] ;arb from head/tail?
      [xz  (map (rcurry fill-rhs #\0 8) arb)] ) ;
    (map
      [flow list->str (rcurry str->int/system 2)] ;
      xz
) ) )

(def/va (rgb->565 rgb [out-hex? F])
  (let-values
    ([(r g b) (redu values rgb)])
    (letn
      ( [r5 (pow 2 [- 5 8])] [r6 (pow 2 [- 6 8])] ;
        [conv (lam (rat n) [fixnum (* rat n)])]
        [resl (+ (conv r5 b) (* (conv r6 g) [pow 2 5]) (* (conv r5 r) [pow 2 11]))] ;?
        [resl (if out-hex? (str "0x" (int->str/system resl 16)) resl)] )
      resl
) ) )

; math

(def =0? (curry eq 0))
(def =1? (curry eq 1))
(def >0  (curry < 0))
(def <0  (curry > 0))
(def >1  (curry < 1))
(def <1  (curry > 1))
(def >=0 (curry <= 0))
(def <=0 (curry >= 0))
(def >=1 (curry <= 1))
(def <=1 (curry >= 1))

(def (not= a b) (not (= a b))) ;!==
(def [!=0 x]    (not [=0 x]))

(def (len0? x)  (eq 0 (len x)))
(def [len>0  x] (>0  (len x)))
(def [len<0  x] (<0  (len x)))
(def [len>=0 x] (>=0 (len x)))
(def [len<=0 x] (<=0 (len x)))
(def [len1   x] (eq 1 (len x)))
(def [len>1  x] (>1  (len x)))
(def [len<1  x] (<1  (len x)))
(def [len>=1 x] (>=1 (len x)))
(def [len<=1 x] (<=1 (len x)))

;(float-len 123.123123) -> 6
(def (float-len flo)
  (let ([xs (str-divide (str flo) ".")])
    (if [>= (len xs) 2]
      (len* (cadr xs))
      0
) ) )

(def (xor . xs)
  (def (xor2% a b) ;logical ;(bitwise-xor 1 1 2 2 2 2 3 3 3)
    (if~ [eq a b] F T)
  )
  (redu~ xor2% [map not xs]) ;not issue when: (xor x)
)

;(.% 123.1234 10.0) ;->3.1234
(def/va (.% num [mod 10.0])
  (let ([~quot (./ num mod)]) ;
    (* mod (- ~quot (floor ~quot))) ;
) )

(def/va (avg% ns [n0 0] [f +] [g /]) ;* pow/ 4 2
  (def (~ ns ret n)
    (if [nilp ns]
      (g ret n) ;
      (let/ad ns
        (~ d (f a ret) (fx1+ n)) ;
  ) ) )
  (~ ns n0 0) ;0
)

(def (avg . xs) ;@
  ; (/ ;
    ; (redu~ + xs)
    ; (len xs) )
  (avg% xs)
)

(def (.avg . xs)
  (avg% xs 0.)
)

(def (cube-avg . xs)
  (avg% xs 1. * (lam (x y) [pow x (./ y)]))
)

(def ./
  (case-lam
    ([a] (/ 1. [exa->inexa a])) ;
    (xs
      (foldl (lam (a b) (/ a [exa->inexa b])) [exa->inexa (car xs)] (cdr xs))
) ) )

(def %
  (case-lam
    [(x) (inexa (/ x 100))]
    [(x . ys) (foldl mod x ys)]
) )
(def (.* . xs)
  (foldl * (exa->inexa [car xs]) (cdr xs))
)
;(def .* (compose exa->inexa *))
(def .- (compose exa->inexa -))
(def .+ (compose exa->inexa +))

(def (sum xs)
  (redu + xs)
)

(def (pow . xs)
  (if [nilp (cdr xs)]
    (expt (car xs) 2) ;
    (fold-left expt (car xs) (cdr xs))
) )

(def (pow/ n m)
  (pow n (/ 1. m)) ;expt
)

(def/va (pow-root m [= (rcurry ~= 15)] [n0 3] [maxTimes 10000])
  (def (~ n i)
    (let ([tmp (log m n)]) ;
      (if~
        [eq i maxTimes] n
        [= tmp n] n
        (~ [avg% (list n tmp)] (fx1+ i))
  ) ) )
  (~ n0 0) ;
)

(def/va (in-range num s e [lt <=] [lt2 nil]) ;case?
  (let ([lt2 (if (nilp lt2) lt lt2)])
    (if [and (lt s num) (lt2 num e)] T F)
) )

(def (float->fix flo) (flonum->fixnum [round flo]))

(def (fixnum num)
  (let ([rnd (round num)])
    (if [flonum? rnd]
      (flonum->fixnum rnd)
      rnd
) ) )

(def (max-min nums)
  (let/ad nums
    (def (~ xs mx mn)
      (if [nilp xs] (list mx mn)
        (let/ad xs
          (if~
            [> a mx]
              (~ d a mn)
            [< a mn]
              (~ d mx a)
            (~ d mx mn)
    ) ) ) )
    (if (nilp nums) nil ;
      [~ d a a]
) ) )

(def (not-exist-meet? g xs)
  (def (once ys x)
    (if (nilp ys) T ;
      (if (g x (car ys)) F
        [once (cdr ys) x]
  ) ) )
  (def (_ ys x)
    (if (nilp ys) T ;
      (if (once ys x)
        [_ (cdr ys) (car ys)]
        F
  ) ) )
  (_ (cdr xs) (car xs))
)
(def (!==  . xs) [not-exist-meet? =   xs])
(def (!eql . xs) [not-exist-meet? eql xs])

(def (reset-randseed) ;reset-random-seed
  (random-seed (time-nanosecond (current-time)))
)

(def (pow-num? x) ;int
  (if (eq 0 [& x (1- x)]) T
    F
) )

(def (num-end-with num xx) ;int
  (letn ([xx-len (n-digits xx)] [tmp (pow 10 xx-len)])
    (eq xx (mod num tmp))
) )

(setq
  *max-deviation* (- [expt (sqrt 2) 2] 2) ;~ > 4e-16
  *max-deviation-ratio* *max-deviation*
  ; (/ ;
    ; (1-
      ; (/
        ; (pow (sqrt 2)) ;
        ; 2 ) ) ;
    ; 2 ) ;
)

(def/va (~= a b [num-prec F]) ;(rcurry ~= 15) ;a b?
  (let
    ( (max-deviation
        (if num-prec
          [/ 1. (pow 10. num-prec)]
          *max-deviation-ratio* ;~ > pow 10 16
    ) ) )
    (< ;
      (abs
        (1-
          (/ a b) ;
      ) )
      max-deviation
) ) )

(def distance
  (case-lam
    ( [p1 p2] ;(dis '(1 2 3 4) '(2 3 4 5)) ;frm p1 to p2: p2-p1
      (if [eq (len p1) (len p2)] ;fill 0? ;nil? [_ p2]
        (sqrt
          [apply + (map [lam(x y)(pow(- x y))] p2 p1)] )
        nil
    ) )
    ([p2] [distance (nlist% '(0) (len p2)) p2])
) )

(def (min-prime-factor n) ;%? factorize prime-num?
  (let ([max. (sqrt n)] [failsym F]) ;
    (def (_ tmp)
      (if~
        (< max. tmp)
          failsym
        [eq (% n tmp) 0] ;
          tmp
        [_ (+ tmp 2)] ) ) ;
    (if~
      [odd? n]
        [_ 3]
      (eq n 2)
        failsym ;for prime-num?
      2
) ) )
(alias min-factor min-prime-factor)

(def (factors n)
  (def (_ factors n) ;
    (let ([factor (min-factor n)]) ;
      (if factor
        [_ (cons factor factors) (quot n factor)]
        (cons n factors) ;
  ) ) )
  (_ nil n)
) ;(cost (factors 40224510201988069377423)) ;->113ms

;(self-act pow num n) => target
(def/va (self-act f num [n 2]) ;@
  (def (_ ret i)
    (if~
      (eq  i n) ret
      (fx< i n)
        [_ (f ret num) (fx1+ i)]
        (error "n in self-act, should be >= 1" n)
  ) )
  (_ num 1)
)

;(rev-calc pow target) =(checker)=> x
;(cube-root 27.) is very slow
(def/va (rev-calc fx tar [= ~=] [x0 2]) ;[exa? T] ;todo: f-xs=y... for +-*/
  (def (_ nex x pre) ;
    (let ([resl (fx x)]) ;
      (if~
        [= resl tar] ;(inexa
          x ;)
        [> resl tar] ;any>
          [_ x (avg pre x) pre] ;..
        [_ nex (avg nex x) x]
  ) ) )
  [_ tar x0 0] ;
)

; end of math

(def (fold g xs) ;(redu g (cons x xs))
  (if~
    [nilp xs] nil
    [cdr-nilp xs] (car xs)
    (foldl g (car xs) (cdr xs)) ;
) )

;(fold% g x y ... xs)
(def (fold% g . paras) ;(redu g (cons x xs))
  (letn
    ( [ls (last paras)]
      [r-rest (rcdr paras)] ;
      [xs (foldr cons ls r-rest)] )
    (if~
      [nilp xs] nil ;
      [cdr-nilp xs] (car xs)
      (foldl g (car xs) (cdr xs)) ;
) ) )

;(foldl-n n g xs)
(def (foldl-n n g xs)
  (let ([n2 (fx1- n)])
    (def (_ xs ret i)
      (if (eq i 0)
        (foldl g ret xs)
        (_ [list-tail xs n2]
          (foldl g ret [list-head xs n2])
          (fx- i n2)
    ) ) )
    (_ (cdr xs) (car xs) [fx- (len xs) n])
) )

; modules

; on lisp: best lrec grip with-gensym with-db fnif setf rplca match/lookup proc ATN

(def (clean-choose)
  (setq *paths* nil)
)

;F when no resl
;todo: collect resls, not only one, maybe we could get at most n resls
(def/va (choose% xs [once? T]) ;
  (def (~ choices) ;choose
    (if (nilp choices) [fail]
      (let ([choice (car choices)] [rest (cdr choices)])
        (call-with-current-continuation
          (lam [cc] ;
            (push
              (lam () [cc (~ rest)]) ;
              *paths* )
            choice ;
  ) ) ) ) ) ;(def fail nil)
  (let ([failsym F])
    (call-with-current-continuation
      (lam [cc] ;
        (setq fail
          (lam ()
            (if [nilp *paths*] ;
              (if once? failsym [cc failsym]) ;can stop when all choices are checked
              (let ([a (car *paths*)]) ;get car bef set to cdr
                [setq *paths* (cdr *paths*)]
                (a) ;
    ) ) ) ) ) )
    [~ xs]
) )

(def/va (true-choose xs [once? T]) ;2~20x@
  (def (~ choices) ;choose
    (call-with-current-continuation
      (lam [cc]
        (setq *paths* ;
          [append *paths* ;
            (map ;
              (lam (choice)
                (lam () [cc choice]) )
              choices
        ) ] )
        [fail]
  ) ) )
  (call-with-current-continuation ;
    (lam [cc]
      (setq fail ;
        (lam ()
          (if (nilp *paths*)
            (if once? F [cc F]) ;
            (let ([p1 (car *paths*)])
              [setq *paths* (cdr *paths*)]
              (p1) ;
  ) ) ) ) ) )
  [~ xs]
)

(def/va (chooses xs [n 1] [rep? T] [once? T]) ;!= one?
  (def (~ ret xs i)
    (if (fx> i n) ret
      (let ([c (choose xs once?)])
        (~ (cons c ret)
          (if rep? xs [remov-1 c xs]) ;
          (fx1+ i)
  ) ) ) )
  (~ nil xs 1) ;seq?
)

;on lisp

(def (infix->prefix xs)
  (def (_ ret xs)
    (if (nilp xs) ret
      (if (cdr-nilp xs) [error "xs length not proper" xs] ;infix->prefix] ;
        (_ (list (car xs) ret [~ (cadr xs)])
          (cddr xs)
  ) ) ) )
  (def (~ x)
    (if (consp x)
      (_ [~ (car x)] (cdr x))
      x ;nump ign, record
  ) )
  (~ xs)
)

(def (evenp n)
  (fx= (mod n 2) 0)
)

(def (prim-num? n)
  (if~ (< n 2) F
    (< n 4) T
    (even? n) F
    (< n 9) T
    (fx= 0 (mod n 3)) F
    (let ([r (sqrt n)]) ;floor?
      (let loop ([f 5]) ;22 25 26
        (if (<= f r) ;
          (if~
            [fx= 0 (mod n f)]       F
            (fx= 0 [mod n (fx+ f 2)]) F
            [loop (fx+ f 6)] )
          T ;
      ) )
) ) )

(def (prime s i) ;i
  (def (~ ret s i)
    (if (fx< i 1) ret ;
      (if (prim-num? s)
        (~ s (+ 2 s) (fx1- i)) ;
        (~ ret (+ 2 s) i)
  ) ) )
  (let( [b (even? s)]
        [b2 (< s 3)] ) ;
    (~
      2 ;
      (if b (1+ s)
        (if b2 3 s) )
      (fx- i (if b2 1 0))
) ) )

(def primes ;todo _ s e
  (lam [s n]
    (def (~ s n ret)
      (if~
        (fx< n 1) ret ;
        (prim-num? s) ;?
          (~ (+ 2 s) (fx1- n) (cons s ret))
        (~ (+ 2 s) n ret)
    ) )
    (let
      ( [b2  (< s 3)]
        [b (even? s)] ) ;
      (~
        (if b (fx1+ s)
          (if b2 3 s) )
        (- n (if b2 1 0))
        (if b2 '(2) '())
) ) ) )

;(cost (prime (1-[redu~ * (primes 2 13)]) 1))
;402245102020351 is the nth? prime-num start from 2 ?

;(euler 1323) -> 756
(def (euler num)
  (let ([f (lam (p) (- 1 (/ p)))])
    (foldl * num
      (map (lam (xn) (f (car xn)))
        (compress (qsort (factors num) >))
) ) ) )

(def n-digits ;integer-length 128 2
  (case-lam
    ([num m] ;@ not for float
      (def (_ num n)
        (let ([quot (quotient num m)]) ;@ 1 2 4 2 1
          (if [< quot 1] n
            [_ quot (fx1+ n)] ;fx
      ) ) )
      (_ num 1) )
    ([num] (n-digits num 10))
) )

(def/va
  (digest% xs [level 12] ;7, 8~12
    (doer
      (lam (x y)
        ;(+ [* (+ (sin x) (sin y)) 2] 5) ;1~9
        ;[+ (sin (* [+ (sin x) 2] (1+ y))) 2] ;*4+5
        (+ 5. [* 4. (sin (* (sin x) (fx1+ y)))]) ;1~9 ;*3+4?
  ) ) )
  (let ([factor (pow 10. level)]) ;8~13 front-part
    ([flow (rcurry * factor) round int] ;? int *
      ;(id ;fold% doer
        (fold% doer 1. xs) ;need seq ;foldl ;rec
        ;nil
) ) ) ;)

(def (leap-year? yr)
  (or (=0 [% yr 400])
    (and
      (=0 [% yr 4])
      (!=0[% yr 100])
) ) )

; matrix: rows columns

;(make-matrix '(3 4 5) 1)
(def (make-matrix dimensions val) ;dimension
  (letn ([ln (redu * dimensions)] [xs (nx->list ln val)]) ;0?
    (redu list->matrix (cons xs [rev (cdr dimensions)])) ;
) )

;(list->matrix '(1 2 3 4 5 6) 1 2)
(def (list->matrix xs . dims) ;flat?
  (def (~ xs dims)
    (if [nilp dims] xs
      (let/ad dims ;
        [~ (group xs a) d] ;0? group-by
  ) ) )
  (~ xs dims)
)

(def (mt/dimens mt)
  (def (~ ret xs)
    (if [lisp xs]
      [~ (cons (len xs) ret) (car xs)]
      ret
  ) )
  [rev (~ nil mt)] ;
)

;mt/max-dimens
(def (mt/max-dimens . mts) ;
  (redu (curry map max) (map mt/dimens mts)) ;
)

(def (mt/n-rows    mt) (len mt))
(def (mt/n-columns mt) (len (car mt)))

(def/va (mt/fmt mt dims [val 0]) ;
  (def (~ mt dims)
    (if [nilp dims] mt
      (letn
        ( [m  (car dims)]
          [ln (len mt)]
          [mr (- m ln)] ;
          [b  (> mr 0)]
          [n  (if b mr 0)] )
        (if b
          (append
            (map (rcurry ~ (cdr dims)) mt) ;@
            (make-matrix (cons n (cdr dims)) val) )
          (ncdr (map (rcurry ~ (cdr dims)) mt) mr) ;
  ) ) ) )
  (~ mt dims)
)

;(mt/calc (curry * 2) mt)
(def (mt/calc f . mts) ;
  (letn
    ( [dims (redu mt/max-dimens mts)] ;
      [mts2 (map (rcurry mt/fmt dims) mts)] )
    (redu (curry map (curry map f)) mts2) ;
) )


;(dot-mul '(1 2 3) '(4 5))
(def (dot-mul v1 v2) ;get-column? ;
  (letn
    ( [dims (mt/max-dimens v1 v2)] ;
      [fmt (lam (v) (mt/fmt v dims))] ) ;@?
    ;if same len
    (redu + (map * (fmt v1) (fmt v2)))
) )

;(mt/get-column (make-matrix '(3 4) 1) 2)
(def (mt/get-column mt n)
  (map (rcurry nth n) mt)
)

(def (mt/flip mt) ;tl ;tr top left ;transposition
  (redu (curry map list) mt)
)

(def (vec-mul-rev~flipped~mt% ve mt) ;
  (def (~ ret xs)
    (if [nilp xs] ret
      (let/ad xs
        [~ (cons (dot-mul ve a) ret) d]
  ) ) )
  (~ nil mt)
)

(def (mt* mt mt2) ;mxs sxn
  (let ([~flip-mt2 (rev (mt/flip mt2))])
    (map (lam (ve) (vec-mul-rev~flipped~mt% ve ~flip-mt2)) mt)
) )

(def (mt/inversable? mt) (not [= (mt/det mt) 0])) ;m=n?

;https://www.shuxuele.com/algebra/matrix-determinant.html
;(setq m66 (list->matrix (range 36) 6))
(def (mt/det mt)
  (let ([xz (cdr mt)])
    (def (~ ret row i) ;
      (if [nilp row] ret
        (let/ad* row
          ([sign (if (odd? i) 1 -1)]) ;
          (~
            (+ ret
              (* ;sign a
                [mt/det
                  (map [lam (x) (remov-nth x i)] xz) ]
                a sign
            ) ) ;
            d (1+ i)
    ) ) ) )
    (if [nilp xz]
      (caar mt)
      [~ 0 (car mt) 1] ;1
) ) )

;(mt/A* m33)
(def (mt/A* mt) ;(-1)^(+ i j)
  (def (~ mt i j)
    (map (lam (x) (remov-xth x j)) ;remov-xth
      (remov-xth mt i)
  ) )
  (def (~comple mt i j)
    (* (if [even? (+ i j)] 1 -1)
      (mt/det (~ mt i j)) ;
  ) )
  (def (~comples mt n) ;@
    (collect (i n)
      (collect (j n) ;m=n
        (~comple mt i j)
  ) ) )
  (let ([tmp (~comples mt (len mt))])
    (mt/flip tmp)
) )

(def (mt/rank mt)
  (let
    ([n (redu min (mt/dimens mt))])
    (def (~ mt n)
      (if [eq n 0] 0 ;
        (letn
          ( [mt2 (mt/fmt mt (list n n))] ;
            [det (mt/det mt)] )
          (if (= det 0) ;
            [~ mt2 (1- n)]
            n
    ) ) ) )
    (~ mt n)
) )

(def (mt/inverse mt)
  (letn
    ( [a* (mt/A* mt)] ;
      [det (mt/det mt)] )
    (if [= det 0] nil ;
      (mt/calc (lam (x) (/ x det)) a*) ;
) ) )

;matrix

;(def (y=fx paras x) (redu +(map * paras(~range 1 (len paras) (lam (n) [* x n]))))) ;@
(alias y=fx list->int/scale)

;(y=fx->paras '(pt pt2 pt3 ...))
(def (y=fx->paras pts) ;cost ms: x5 1, x6 10, x7 100, x8 1s ;n^2... ;for for
  (letn
    ( [n  (len pts)]
      [xs (map car pts)]
      [ys (map cadr pts)]
      [gen  (lam (x) (~range 1 n (lam (~) (* x ~))))] ;
      [xz   (map gen xs)]
      [resl (mt* (mt/inverse xz) (map list ys))] ) ;
    (map car resl)
) )

(def (strnum- . snums)
  (number->string (redu~ - (map string->number snums)))
)
(def (strnum+ . snums)
  (number->string (redu~ + (map string->number snums)))
)

(def/va (max-cnt-of-same xs [lt <])
  (if [nilp xs] 0
    (nth
      [qsort
        (compress [qsort xs lt] =) ;
        (lam (x y) [> (nth x 2) (nth y 2)]) ] ;
      1 2
) ) )

;math end

(def [len-1 x] (1- [len x]))

(def (find-ref% xs x st ed)
  (let ([ed (if(nilp ed)(len-1 xs)ed)][= (eq/eql x)])
    (def (_ xs x i)
      (if [= x (car xs)] ;
        i
        (if [>= i ed]
          nil
          (_ (cdr xs) x (1+ i))
    ) ) )
    (_ xs x st)
) )

(def (remov-nil xs)
  (def (_ xs)
    (if (nilp xs) nil
      (let ([a (car xs)] [d (cdr xs)])
        (if (nilp a)
          [_ d]
          (cons a [_ d]) ;
  ) ) ) )
  [_ xs]
)
(def (~remov-nil xs)
  (def (_ xs ret)
    (if (nilp xs) ret
      (let ([a(car xs)] [d(cdr xs)])
        (if (nilp a)
          [_ d ret]
          [_ d (cons a ret)]
  ) ) ) )
  [_ xs nil]
)

(def/va (remov-1 x xs [g nil]) ;
  (let ([g (if (nilp g) (eq/eql x) g)]) ;
    (def (_ xs)
      (if (nilp xs) nil
        (let ([a(car xs)] [d(cdr xs)])
          (if (g a x) d
            (cons a [_ d])
    ) ) ) )
    (_ xs)
) )
(def/va (remov-all x xs [g nil])
  (let ([g (if (nilp g) (eq/eql x) g)])
    (def (_ xs)
      (if (nilp xs) nil
        (let/ad xs
          (if (g a x) ;
            [_ d] ;remov
            (cons a [_ d]) ;keep
    ) ) ) )
    (_ xs)
) )

(def/va (remov-n x xs n [g nil])
  (let ([g (if (nilp g) (eq/eql x) g)])
    (def [_ xs n]
      (if [or (eq n 0) (nilp xs)] xs ;
        (if~ [< n 0] [remov-all x xs g] ;
          [eq n 1] [remov-1 x xs g]
          (let ([a (car xs)] [d (cdr xs)])
            (if (g a x)
              [_ d (1- n)]
              (cons a [_ d n]) ;
    ) ) ) ) )
    [_ xs n]
) )

(def remov
  (case-lam
    ([x xs n g] ;@
      (if [< n 0]
        (if [nilp x]
          (remov-nil xs)
          (remov-n x xs n g) ) ;(remov-all x xs)
        (remov-n x xs n g)
    ) )
    ([x xs n] (remov x xs n nil)) ;
    ([x xs] (remov x xs -1))
) )

(def/va (remov-xths% xs xths [base 0]) ;% xths [base 0]
  (def (_ xs xths n) ;i
    (if (nilp xs) nil
      (if (nilp xths) xs
        (if [eq (car xths) n]
          [_ (cdr xs) (cdr xths) (1+ n)]
          (cons (car xs) [_ (cdr xs) xths (1+ n)])
  ) ) ) )
  (_ xs xths base) ;
)

(def (remov-nth% xs . nths)
  (def (_ xs nths n)
    (if (nilp xs) nil
      (if (nilp nths) xs
        (if [eq (car nths) n]
          [_ (cdr xs) (cdr nths) (1+ n)]
          (cons (car xs) [_ (cdr xs) nths (1+ n)])
  ) ) ) )
  (_ xs [sort < (filter >0 nths)] 1) ;
)

(def (remov-xth xs . xths)
  (def (_ xs xths n)
    (if (nilp xs) nil
      (if (nilp xths) xs
        (if [eq (car xths) n]
          [_ (cdr xs) (cdr xths) (1+ n)]
          (cons (car xs) [_ (cdr xs) xths (1+ n)])
  ) ) ) )
  (_ xs xths 0) ;
)

(def (remov-nth xs . nths)
  (def (_ xs nths n)
    (if (nilp xs) nil
      (if (nilp nths) xs
        (if [eq (car nths) n]
          [_ (cdr xs) (cdr nths) (1+ n)]
          (cons (car xs) [_ (cdr xs) nths (1+ n)])
  ) ) ) )
  ;(_ xs [sort < (filter >0 nths)] 1) ;
  (_ xs nths 1) ;
)

(def [permutation xs] ;(_ n xs-range n0) ;how ab repeating cases?
  (def (_ ret xs ys)
    (if (nilp xs) ret
      (letn
        ( [a (car xs)]
          (d (cdr xs))
          (ts (remov-1 a ys)) ;
          [zss (permutation ts)] )
        (if (nilp zss) `([,a]) ;
          (_ (append~ ret [map (curry~ cons a) zss]) d ys)
  ) ) ) )
  (_ nil xs xs)
)

;make-groups
(def [combinations xs n] ;todo [full-combinations/subsets '(1 2)]~>'([1 2][1][2][])
  (def (_ xs n)
    (if~
      [eq n 0] nil
      [eq n 1] (map list xs)
      [>= n (len xs)] (list xs) ;
      (append~ ;
        [_ (cdr xs) n]
        (map [curry~ cons (car xs)] ;
          [_ (cdr xs) (1- n)]
  ) ) ) )
  (_ xs n)
)

(def (permu-n xs n)
  (redu~ append~
    (map permu (combinations xs n)) ;
) )

(def_ (subsets xs) ;_ '(1 2 3) ~> '(() (1)(2)(3) (1 2)(2 3)(1 3) (1 2 3))
  (if (nilp xs) (list nil)
    (let ((rest [_ (cdr xs)]))
      (append rest
        (map [curry cons (car xs)] rest)
) ) ) )

(def/va (deep& [fx id] [fxs id] xs) ;?
  (def (_ x)
    (if~
      [nilp  x] nil
      [consp x] (fxs [map _ x]) ;@
      (fx x)
  ) )
  (_ xs)
)

;(deep-reverse '(1(2 3)4)) ;-> '(4(3 2)1)
(def (deep-reverse xs)
  (def (d-rev xs)
    (if~
      [nilp xs] '() ;
      [pair? xs]
      (map d-rev
        (rev xs) ) ;
      else xs
  ) )
  (d-rev xs)
)

;(group '(1 2 3 4 5 6) 3)
(def [group xs per] ;?(= m per) (group '(1 2 3 4 5 6) 3 1)
  (let ([m (if [<= per 0] 1 per)]) ;-2?
    (def (_ ret xs)
      (if (nilp xs) ret
        (let ([aa (head% xs m)] [dd (tail% xs m)]) ;% ;(head-tail xs m)
          [_ (cons aa ret) dd]
    ) ) )
    (rev [_ nil xs]) ;
) )

(def (arb-group xs . ns) ;arbitrarily: (_ xs 5 6 5)
  (def (_ xs n ms tmp ret) ;ret tmp xs n ns
    (if (nilp xs)
      (cons tmp ret) ;
      (let/ad xs
        (if (nilp ms)
          (if (eq 0 n)
            (cons tmp ret)
            [_ d (1- n) nil (cons a tmp) ret] )
          (if (eq 0 n)
            [_ xs (car ms) (cdr ms) nil (cons tmp ret)]
            [_ d (1- n) ms (cons a tmp) ret]
  ) ) ) ) )
  [deep-rev (_ xs (car ns) (cdr ns) nil nil)] ;
)

;(groups (range 32) 2 8)
(def (groups xs . ns) ;
  (def (_ xs ns)
    (if (nilp ns) xs
      (_
        (group xs [car ns])
        [cdr ns]
  ) ) )
  (_ xs ns)
)

(def (prune g xs)                           ;rec remov-if satisfy g ;!keep
  (def (_ xs ret)
    (if [nilp xs] (rev ret)
      (let ([a (car xs)][d (cdr xs)])
        (if [consp a] ;
          (_ d (cons [_ a nil] ret))
          (_ d [if (g a) ret (cons a ret)]) ;
  ) ) ) )
  (_ xs nil)
)

;(map-all list '(1 2) '(4) '(5 6)) ;~> 4 lists
(def [map-for-combinations g . xz]
  (def (~ ret tmp0 xs0 xz)
    (def [_ ret tmp xs xz]
      (if (nilp tmp)
        (if (nilp xz)
          (map (curry redu g) ;lam
            (deep-rev ret) ) ;
          [~ nil [rev ret] (car xz) (cdr xz)] ) ;
        (if (nilp xs)
          [_ ret (cdr tmp) xs0 xz] ;
          [_ (cons [cons(car xs)(car tmp)] ret) tmp (cdr xs) xz] ;
    ) ) )
    [_ ret tmp0 xs0 xz]
  )
  [~ nil (list nil) (car xz) (cdr xz)] ;remov nil xz
) ;4x+ slow
;

(def (sym-explode sym) ;[explode 'asd] ~> '[a s d]
  (map string->symbol [str->ss (sym->str sym)])
)

(setq *alphabet* (str->ss "abcdefghijklmnopqrstuvwxyz"))

;

(def (replace-in xs x y)
  (let ([g (eq/eql x)])
    (map
      (lam (a) (if [g a x] y a))
      xs
) ) )

;(dmap [lam(x)(if[nilp x]0 x)] xs)
;(def +.ori +) ;+.0

(def (sum-of-tree@ xs) ;@ < redu~ < +
  (redu~ + xs)
  ; (def (_ x ret)
    ; (if~
      ; (num?  x) (+ ret x) ;
      ; (atomp x) ret ;nilp
      ; (_ (car x)
        ; [_ (cdr x) ret]
  ; ) ) )
  ; (_ xs 0)
)
(def (sum-of-list xs)
  (def (_ x ret)
    (if~
      (nilp x) ret
      (let ([a (car x)])
        (_ (cdr x)
          (if (num? a) (+ ret a) ret) ;
  ) ) ) )
  (_ xs 0)
)
(def (my+ . xs) (sum-of-list xs)) ;2.5x slower than ori +
;(def + my+) ;to test (fib0 42) ;need to be restored bef reload this script

;(_ x n g x0) ;x*n x+..+x
(def (fast-expt-algo x n g x0) ;g need to meet the Commutative Associative Law
  (def (_ n)
    (if~
      (= n 0) x0 ;rev-calc?
      (= n 1) x ;(* x x0) ==> x ;?
      (letn
        ( (m [_ (>> n 1)]) ;half
          (y [g m m]) ) ;even
        (if (fxeven? n) y
          [g y x]
  ) ) ) )
  (_ n)
) ; N mod z ?=> a^q*s^w*d^e mod z => ... ; encrypt: 椭圆曲线加密 ; 所有基于群幂的离散对数的加密算法

(def/va (fast-expt g x [n 1]) ;not for pow ;> =
  (def (_ n)
    (if~
      [fx> n 1] ;fx>= 2
        (letn
          ( [m (_ [>> n 1])]
            [y (g m m)] )
          (if (fxeven? n) y ;fx
            [g y x]
        ) )
      [eq n 1] x ;eq <- =
      (error "n in fast-expt, should be >= 1" n)
  ) )
  (_ n)
)

(def (matrix-unitlen m) [len (car m)])

(def (matrix-unit n) ;vec?
  (def (once ret m i)
    (def (_ ret m)
      (if (< m 1) ret
        [_ (cons 0 ret) (1- m)]
    ) )
    [_ [cons 1 (xn->list 0 i)] m] ;
  )
  (def (_ ret i m)
    (if [< m 0] ret
      [_ (cons(once nil m i)ret) (1+ i) (1- m)]
  ) )
  (_ nil 0 (1- n))
)

(def (matrix-unitof m) [matrix-unit (matrix-unitlen m)])

(def (matrix-pow m n)
  (fast-expt-algo m n matrix-mul (matrix-unitof m)) ;(fast-expt-algo m n mat-mul '[(1 0)(0 1)])
)

(define (fib0 n)
  (define (~ n)
    (case n
      ([0 1] n) ;
      (else
        (+ [~ (-  n 2)] ;
           ;[~ (-  n 1)]
           [~ (fx1- n)]
  ) ) ) )
  (~ n)
)
;(cost (fib0 42)) ;realtime = 1.111~1.176 s
;gmp: (fib 1E) just 1s

(def (fib n)
  (def (fibo pre pos n) ;prev next cnt
    (caar
      (matrix-mul  ;
        (if [fx> n 0] ; or ret: if odd? n: positive, negative;
          (matrix-pow `([ 0  1]
                        [ 1  1]) n) ;matrix may slower than paras
          (matrix-pow `([-1  1]
                        [ 1  0]) (fx- n)) )
        `([,pre]
          [,pos])
  ) ) )
  (fibo 0 1 n)
)
;(elapse(fib 200000)) ;=> elapse = 0.082 s
;(cost (chk 100000 fib 42)) ;-> 225ms

(def (fac2 s e)
  (let
    ([Init 1])
    (def [~ ret i]
      (if
        [> i e] ret
        [~ (* ret i) (fx1+ i)]
    ) )
    [~ Init s]
) )

(def (fac n)
  (let
    ([S 1]) ;2 ;
    (fac2 S n)
) )
;(elapse(fac 50000)) ;=> elapse = 1.372~1.4 s

(def (round% x) ;
  (let ([fl (floor x)])
    (if [>= (- x fl) 0.5] ;
      (1+ fl)
      fl
) ) )

;(_ 123.5) ;floor?
(def myround ;when input exa flt, is (4~)6x ~ than round
  (case-lam
    ([flt] ;(exact (#%round [inexa flt]))
      (#%round flt) ) ;when input inexa flt, is 1.1(~4.5)x @ than round
    ([flt nFlt] ;if exa should ret int
      (let ( ;[conv (if [and (exact? flt) (<= nFlt 0)] exact id)] ;
          [fac (pow 10. nFlt)] ) ;(conv ;@
        (/ [round% (* fac [inexa flt])] fac) ;
) ) ) )

;matrix:
;'(1 2 3 4 5 6) --m*3->
;a mat: '((1 2 3)(4 5 6))
;((mat m 3) 1 2 3 4 5 6)
;(_ numForOneRow aFlattenList): (_ 3 (range 6)) -> '((0 1 2)(3 4 5))

;?matlen submat
(def (dotmul da db) ;(1,2,3)*(4,5,6) ;dot-multiply: point1 point2
  (redu~ + (map * da db)) ;
)
(defn convolution1 (m1 m2) ;convolution: matrix1 matrix2
  (redu~ dotmul (map mat2lis (li m1 m2)))
)

;middle-function
(def (pt-mat-mul p m) ;'(1 2 3) '((4 7)(5 8)(6 9))
  (def (_ m)
    (if [nilp (car m)] nil
      (cons [dotmul p (map car m)] [_ (map cdr m)]) ;todo
  ) )
  [_ m]
)

(def (mat-mat-mul ma mb) ;mul-2-matrixes
  (def (_ ma)
    (if (nilp ma) nil
      (cons [pt-mat-mul (car ma) mb] [_ (cdr ma)]) ;
  ) )
  [_ ma]
)

(def (matrix-mul . mts) ;matrix-spot-mul matrixes ;what's the limit?
  (fold-left mat-mat-mul (car mts) (cdr mts))
)

;AI

(def ReLU (curry max 0))

(def (sigmoid x)
  (/ (1+ [exp (- x)]))
)
(def (swish x)
  (* x (sigmoid x))
)

(def/va (nonlin x [deriv? F])
  (if (eq deriv? T)
    (* x [- 1 x])
    (sigmoid x)
) )

; file: load-file-cont-as-str

(def (file? x) (not [file-directory? x]))

;(file-name "c:/my.path/file.ex.ext") -> file.ex
;(file-name "file.ex") -> file
(def (file-name s-file)
  (letn
    ( [file (last [str-divides s-file '("/" "\\")])]
      [tmp (str-divide file ".")] ;
      [d   (cdr tmp)] )
    (if (eql file "") nil
      (if [nilp d] tmp
        [strcat/sep (rcdr tmp) "."] ;(str-repl st ss sd n rev?)
) ) ) )

;(file-ext "c:/my.path/file") -> nil ;/ \\
(def (file-ext s-file)
  (letn
    ( [tmp (str-divide (last [str-divides s-file '("/" "\\")]) ".")]
      [d   (cdr tmp)] )
    (if [nilp d] nil
      (last d)
) ) )

(def/va (rand-filename [name-len 8] [ext ".txt"] [chars *chs-letters*]) ;
  (str (rand-list chars name-len) ext)
)

(define (read-file-0 file-name) ;guenchi
  (let ([p (open-input-file file-name)]) ;
    (let loop ([lst nil] [c (read-char p)])
      (if [eof-object? c]
        (begin
          (close-input-port p)
          (list->string (reverse lst)) )
        (loop (cons c lst) (read-char p))
) ) ) )

(def/va (load-file file [codec "utf-8"]) ;
  (let*
    ( [tx (make-transcoder [iconv-codec codec] (eol-style crlf) (error-handling-mode replace))] ;
      [p  (open-file-input-port file (file-options no-fail) (buffer-mode block) tx)] ;F <~ tx
      [getter read-char] )
    (def (_ ret)
      (let ([c (getter p)])
        (if (eof-object? c)
          (bgn (close-input-port p) [rev ret])
          [_ (cons c ret)]
    ) ) )
    [list->str (_ nil)]
) )

(def (load-bin-file file) ;read-bin-file->bytevector/u8-list/char-list/string
  (let*
    ( ;[tx (make-transcoder (iconv-codec "gbk") (eol-style crlf) (error-handling-mode replace))] ;?
      [p  (open-file-input-port file (file-options no-fail) (buffer-mode block) #f)] ;F <~ tx
      [getter get-bytevector-all] ;<~ read-char
      [ret (getter p)] ) ;
    (close-input-port p)
    ;(list->str (map int->char
      (bytevector->u8-list ret)
    ;) ) ;
) )
;(u8-list->bytevector (map char->int (str->list

(def/va (save-bin-file cont file)
  [if (file-exists? file) (delete-file file)]
  (letn
    ( [p  (open-file-output-port file (file-options no-fail) (buffer-mode block) F)]
      [writer put-bytevector] ) ;-some?
    (writer p [u8-list->bytevector cont]) ;string->bytevector
    (close-output-port p)
) )

(def (save-file0 cont file) ;
  [if (file-exists? file) (delete-file file)]
  (let ([of (open-output-file file)]) ;
    (write cont of) ;"asd\ndsa\n" print-to-file ?
    (close-port of)
) )

(def/va (save-file cont file [codec "utf-8"]) ;[bin? F])
  [if (file-exists? file) (delete-file file)]
  (let*
    ( (tx ;(if bin? F
        [make-transcoder [iconv-codec codec] (eol-style crlf) (error-handling-mode replace)] ) ;) ;
      [p  (open-file-output-port file (file-options no-fail) (buffer-mode block) tx)] ;
      [writer write-char] ) ;put-bytevector/-some
    (def (_ xs)
      (if (nilp xs)
        (bgn (close-output-port p)) ;
        (let/ad xs ;textual, else put-char?
          (writer a p)
          [_ d]
    ) ) )
    (_ [str->list cont]) ;
) )

;(ls (cwd))
(def cwd current-directory)
(def/va (ls [s-path "./"])
  (directory-list s-path)
)

;(with-str?-nocase "asdqQllkj" "QQ")
(def (with-str? ss sx) ;str-with?/nocase
  (let ([conv str->list])
    (with? (conv ss) (conv sx)) ;
) )
(def (with-str?-nocase ss sx)
  (let ([conv str->list])
    (with?-nocase (conv ss) (conv sx))
) )

;(grep "qq" (ls (cwd)) [ign-case? T])
(def/va (grep sx sz [case? T])
  (let ([str-with (if case? with-str? with-str?-nocase)])
    (filter [rcurry str-with sx] sz)
) )

(ali get-path path-parent)
(ali exist-path? exist-file?)

(def (make-file file) ;.\\asd\\1.txt ;./dsa/2.txt
  (make-file! file)
)

;(path/gnu->win "c:/asd/dsa/x.f")
(def (path/gnu->win ss)
  (str-repl ss "/" "\\")
)

;(path/win->gnu "c:\\asd\\dsa\\x.f")
(def (path/win->gnu ss)
  (str-repl ss "\\" "/")
)

(def (make-file! file) ;T F nil
  (if (exist-file? file) nil ;
    (let ([path (get-path file)])
      (if (exist-path? path)
        (make-file!% file)
        (bgn
          (make-path path) ;
          (make-file!% file)
) ) ) ) )

(def (make-path/win path) ;win ;conv?
  (sys (str "md " [path/gnu->win path] " 2>nul")) ;hide error path/gnu->win
)

(def (make-file!%/win file) ;path?
  (sys (str "type nul>" file))
)

#|
- if exist-file file:
  - backup
    - if exist backup-file:
      - backup back-file ".old" ; if old there, remove the back-file ; so, just keep the old one and the last one
|#
(def/va (write-file! file cont [ext-back ".bak"]) ;.last
  (let ([back (str file ext-back)])
    (if (exist-file? file) ;
      (rename-file! file back) ;
      (make-path (get-path file)) ;
    )
    (write-new-file file cont) ; should delete file first
) )

(def (write-new-file file cont) ;write-new-file/bin
  (let
    ( ;[tx (make-transcoder (iconv-codec "gbk") (eol-style lf) (error-handling-mode replace))] ;to use u8 char
      [p  (open-file-output-port file (file-options no-fail) (buffer-mode block) F)] ) ;F for binary format file
    (put-bytevector p ;cont
      (u8-list->bytevector (map char->int (str->list cont))) ) ;
    (close-port p)
) )
; (def (write-new-file file cont) ; if exist: dele?
  ; (let ([p (open-output-file file)] [xs (str->list cont)]) ;
    ; (def (_ xs)
      ; (if [nilp xs] (close-output-port p)
        ; (bgn
          ; (write-char (car xs) p) ;
          ; (_ (cdr xs))
    ; ) ) )
    ; (_ xs)
; ) )

(def (rename-file! file new)
  (if (exist-file? new)
    (delete-file new) )
  (rename-file file new)
)

(def/va (backup-file! file [ext-back ".bak"])
  (backup-file!% file (str file ext-back))
)

(def (backup-file!% file back)
  (rename-file! file back) ;
)

;(get-file-var "product" "info.txt") ;[] (path/gnu->win "things/special/product/info.txt")
;= \r\n ,
;[rev? F]
(def/va (get-file-var s-var s-file [case? T] [line-sep "\n"] [rev? F]) ;how about zhcn? ;\r\n
  (letn
    ( [conv (if case? id str-downcase)]
      [f (if rev? val->key key->val)] ;eql
      [cont (conv (load-file s-file))]) ;
    (f ;
      (map [compose (rcurry str-divide "=") str-trim-head] ;
        [str-divide cont line-sep] ) ;if win ;down?
      s-var eql
      conv ;
) ) )

;(file/string ss {num 1} [s-path "."] [case? T] [show-ori-when-fail? T] [chk-ext ] [tar-format id])
(def/va
  (files/cont ss
    [s-path "."]
    [case? T] ;[show-ori-when-fail? T]
    [more? T]
    [chk-ext (rcurry mem? '("h" "cpp" "txt" "md" "xls" "html"))] ;"" "json" "conf"
    [tar-format id] )
  (file/cont ss s-path case? more? chk-ext tar-format)
)
(def/va
  (file/cont ss
    [s-path "."]
    [case? T] ;[show-ori-when-fail? T]
    [more? F] ;
    [chk-ext (rcurry mem? '("h" "cpp" "txt" "md" "xls" "html"))] ;
    [tar-format id] ;(rcurry str/sep-chars '[#\x0])
  )
  (letn
    ( [conv (if case? id str-upcase)]
      [ss2  (tar-format (conv ss))] ) ;may not need to eq #\nul
    (def (~ s-path)
      (let
        ( [things (ls s-path)]
          [rel-path (lam (x) [strcat s-path "/" x])] )
        (def (_ ret xs) ;cnt-file?
          (if [nilp xs] ;
            (if (nilp ret) ss ret) ;(if (<= num 0) ret ;
            (let/ad xs
              (if [folder? (rel-path a)]
                (let ((resl [~ (rel-path a)])) ;
                  (if [consp resl] ;
                    (if more?
                      [_ (append resl ret) d] ;
                      (append resl ret) )
                    [_ ret d]
                ) )
                (if [chk-ext (file-ext a)] ; "xlsx" ;[chk-ext (rcurry mem? '["h" "cpp"])]
                  (letn
                    ( [cont (load-file  (rel-path a))]
                      [bool (str-exist? (conv cont) ss2)] ) ;one file search n
                    (if bool
                      (if more?
                        [_ (cons (rel-path a) ret) d] ;
                        (cons (rel-path a) ret) )
                      [_ ret d]
                  ) )
                  [_ ret d]
        ) ) ) ) )
        (_ nil things)
    ) )
    (~ s-path)
) )

(def (diagonal-length x y) [sqrt (redu-map + pow (list x y))])

;theory

; (def (rev~ xs) ;rev!% syn
  ; (reverse! xs)
; )

(def (rcdr xs)
  (def (_ xs)
    (if (nilp (cdr xs)) nil
      (cons (car xs) [_ (cdr xs)])
  ) )
  (_ xs)
) ;a bit slower than (head xs n)

(def (mk-cps g)
  (lam args
    ( [last args] ;
      (redu g
        (rcdr args) ) ;
) ) )
;([(compose-n mk-cps 2) rev] '(1 2 3) list echo)

(def (mk-cps0 g) ;cps相当于做了堆栈交换?
  (lam args
    (let ([r (rev args)])
      ( [car r] ;last
        (redu g
          (rev (cdr r)) ;
) ) ) ) )

; ((lambda (x) (list x (list 'quote x)))
  ; '(lambda (x) (list x (list 'quote x)))))
; ((lam (g) (li g (li 'quo g)))
  ; '(lam (g) (li g (li 'quo g)))))
; ((lam (g) (li g `(',g))) '(lam (g) (li g `(',g)))))
; ((lam (g) `(,g (',g))) '(lam (g) `(,g (',g)))))
; ((lam (g) `(,g '(,g))) '(lam (g) `(,g '(,g)))))

; ((lam (g) `(,g ',g)) '(lam (g) `(,g ',g))))

(def (quine-f g) `(,g ',g)) ;[_ '_] `,_ ' ;(quine 'quine) (ev(quine 'quine)) (eql (quine 'quine) (ev(quine 'quine)))


(defn/defa ev-n (x m) [1]
  (def (_ x n)
    (if~ (> n m) x
      ; (let ([ret (ev x)])
        ; (if~ (eql x ret) x ;?
      [_ (ev x) (1+ n)]
  ) ) ;) )
  (_ x 1)
)
(def (full-eval x) ;
  (def (_ x)
    (let ([ret (try(ev x))])
      (if~ (try-fail? ret) x
        (eql x ret) x
        [_ ret]
  ) ) )
  (_ x)
)

;;church-number: https://www.zhihu.com/question/39930042

;lam-cps, call-cps, def-cps, defn-cps
(ali lam-cps lam-snest)
(ali call-cps call-snest)
(alias defn-cps defn-snest)

(def (nex-prime p)
  (prime p 2) ;
)
(def inc (curry + 1)) ;for church's f, use 1+ is not rooty ?

;(def (zero f) (lam(x) x))
;(def (one f) (lam(x) (f x))) ;((one inc) 0)
; (def (add1 nf)
  ; (lam(f) (lam(x) [f ((nf f) x)] )) )
(defn-snest chur0 (f x)   x)
(defn-snest chur1 (f x)   (f x))
(defn-snest chur2 (f x)   (f (f x))) ;?
(defn-snest chur3 (f x)   ([compose f f f] x))
(defn-snest chur4 (f x)   ([compose-n f 4] x))

(defn-cps church0 (f g x) x)
(defn-cps church1 (f g x) [g x])
(defn-cps church2 (f g x) [(compose-n g 2) x])

(def (chur num) ;num >= 0
  (lam-cps (f x)
    ;([redu compose (xn->list f num)] x) ;
    ([compose-n f num] x) ;
) )
(def (church num . xs) ;num >=? 0
  (lam-cps (f g x)
    ([compose-n g num] x) ;if 0 x
) )
(def chur5 (chur 5))

; (call-snest chur* (mk-chur 123) (mk-chur 3) inc 0)

;todo: chur-*%/n/<=/or

(defn-snest chur+ (c1 c2) ;same
  (lam-snest (f x)
    [(c1 f) ((c2 f) x)]
) )
(defn-snest chur* (m n f) ;fast-expt
  (m (n f))
)

(def (church1+ n . xs) (lam-cps (f g x) [g (([n f] g) x)]))
(def (church1- n . xs) (lam-cps (f g x) [f (([n f] g) x)]))
(defn church+ (c1 c2)
  (lam-cps (f g x)
    [([c2 f] g) [([c1 f] g) x]]
) )
(defn church- (c1 c2)
  (lam-cps (f g x)
    [([c2 g] f) (([c1 f] g) x)]
) )
(defn church* (m n)
  (lam-snest (f g)
    ([m f] ([n f] g)) ;
) )

(defn-snest chur+1 (nf f x) [f ((nf f) x)]) ;inc n
(defn-snest chur-1 (nf  f g x) [f ((nf  g) x)]) ;inc n

;λn w z. ((n λl h. h (l w)) (λd.z)) (λx.x)
(def chur-pred
  (lam-cps [ch g z] ;decr 6的前驱=>5
    ( ( (ch
          (lam [l h]
            (h (l g)) ) )
        (lam [d] z) ) ;l h d ?
      id
    )
    ;(g ((ch g) zero)) ;1+
) )

(defn-snest chur-t   (t f) t)
(defn-snest chur-f   (t f) f)
(defn-snest chur-and (a b) [(a b) chur-f])
(defn-snest chur-or  (a b) [(a chur-t) b])
(defn-snest chur-not (a)   [(a chur-f) chur-t])
(defn-snest chur-xor (a b) [(a (chur-not b)) b])

; pair = \a.\b.\c.c a b
; first = \p.p true
; second = \p.p false
(defn-snest chur-pair (a b c) [(c a) b]) ;
(defn-snest chur-1st (p) (p chur-t))
(defn-snest chur-2nd (p) (p chur-f))
;let empty = pair false false
(defn-snest chur-nil () ((chur-pair chur-f) chur-f))
;list = \a.\b.pair true (pair a b) in
(defn-snest chur-li (a b) ([chur-pair chur-t] [(chur-pair a)b]))

; (def (chur-fib0 n) ;30=*23(+23) ;(((~ ((chur* [(chur* two)three]) [(chur+ two)three])) f) x)
  ; (if ((chur<= n) two) one
    ; ((chur+ [chur-fib0(chur-1 n)]) [chur-fib0((chur- n)2)])
; ) )

(alias yc y-comb)

(define y-comb ;+letrec
  (fn (self)
    ( [fn (f) (f f)]
      (fn (~)
        (self
          (fn arg
            (apply [~ ~] arg) ;
) ) ) ) ) )
;[(yc y-len) '(1 2 3)]

(define (y-len ~)
  (fn [xs]
    (if [nilp xs] 0
      (1+ [~ (cdr xs)])
) ) )

;algo

(def (filter% g xs)
  (def (_ xs)
    (if (nilp xs) nil
      (let ([a (car xs)][d (cdr xs)])
        (if (g a)
          (cons a [_ d]) ;cons mk _ slower than filter
          [_ d]
  ) ) ) )
  (_ xs)
)
(def (filter2 g xs) ;~> '(tagets rests)
  (def (_ xs ll rr) ; ll rr
    (if (nilp xs)
      (list ll rr) ;/pair
      (let/ad xs
        (if (g a)
          [_ d (cons a ll) rr]
          [_ d ll (cons a rr)] ;
  ) ) ) )
  (_ xs nil nil)
)

(def/doc (most-match g? xs) ;_-left
  (def (~ ret xs)
    (if (nilp xs) ret
      (let ([a (car xs)])
        (~(if (g? a ret) a ret)
          (cdr xs)
  ) ) ) )
  (~ (car xs) (cdr xs))
)

(def (maxs . ns)
  (def (_ x m ns)
    (if (nilp ns) (li x m) ;
      (let ([a (car ns)] [d (cdr ns)])
        (cond
          [(> a x) [_ a 1 d]]
          [(< a x) [_ x m d]]
          [else    [_ x (1+ m) d]]
  ) ) ) )
  (if (nilp ns) nil
    (_ (car ns) 1 (cdr ns))
) )

(defn apply/reducing-num (f n)
  (def (_ ret n)
    (if (< n 1) ret
      [_ (f ret n) (1- n)]
  ) )
  (_ nil n)
)

(defn num->lbump-g (n g)
  (def (_ n ret)
    (if~ (< n 0) nil
      (eq n 0) ret
      [_ (1- n) (g ret n)]
  ) )
  (_ (1- n) (g n))
)
(defn num->rbump-g (n g)
  (def (_ n ret)
    (if~
      (eq n 0) ret
      (fx< n 0) nil
      [_ (fx1- n) (g n ret)]
  ) )
  [_ (fx1- n) (g n)]
)

(def num->lbump (rcurry num->lbump-g list))
(def num->rbump (rcurry num->rbump-g list))

; (defn dmap% (g xs)
  ; (def (_ xs ret)
    ; (if (nilp xs) [rev ret]
      ; (let ([a (car xs)][d (cdr xs)])
        ; (if (consp a)
          ; (_ d (cons (_ a nil) ret))
          ; (_ d [cons (g a) ret])
  ; ) ) ) )
  ; (_ xs nil)
; )

(def (list-do xs . fs) ;f g h f g h ...
  (let ([m (len fs)])
    (def (_ xs ret i)
      (if (nilp xs) ret
        [_ (cdr xs)
          (cons [(list-ref fs i)(car xs)] ret)
          (% (1+ i) m) ]
    ) )
    (rev (_ xs nil 0))
) )

;[(deep (curry map g)) xs]
;[(deep 1+) xs]

(def (deep-map g xs) ;deep-map g . xz
  (def (_ xs)
    (if [nilp xs] nil
      (let/ad xs
        (if [consp a] ;
          (cons [_ a] [_ d]) ;flat & bump/hunch ;@
          (cons (g a) [_ d])
  ) ) ) )
  [_ xs]
)

(def (lis-copy xs)
  (vec->lis (lis->vec xs))
)

(def (vec-nilp x) ;
  (if [vecp x]
    (=0 (vec-len x))
    F
) )
;(def num->lis (curry apply/reducing-num cons)) ;
(def num->lis iota)

(def vnil (vec))
(def (vec-car v) (vec-ref v 0))
(def (vecadr v) (vec-ref v 1))

(def (vec-consp v) (and (vecp v) [>0(vec-len v)]))

(defn num->vec (n)   ;vec-flat ;@(lis->vec (range n))
  (let ([ve (mk-vec n)])
    (for (i n)
      (vec-set! ve i i) )
    ve
) )

(def (ve-last ve)
  (vec-ref ve [1- (vec-len ve)])
)

(defn vec-cons (x vy) ;* . xxv
  (if (vecp vy)
    (let ([ve (mk-vec [1+ (vec-len vy)])])
      (vec-set! ve 0 x)
      (vec-copy! ve 1 vy)
      ve
    )
    nil ;
) )
(def [ve-cons* . xxv]
  (letn ([vy (last xxv)][n (len xxv)][m (1- n)])
    (if (vecp vy)
      (let ([ve (mk-vec [+ m (vec-len vy)])])
        (vec-copy! ve 0 (lis->vec [ncdr xxv -1])) ;->lis flat
        (vec-copy! ve m vy)
        ve )
      nil
) ) )
(defn vec-conz (vx y)
  (if (vecp vx)
    (letn ([n (vec-len vx)][ve (mk-vec [1+ n])])
      (vec-copy! ve 0 vx)
      (vec-set! ve n y)
      ve
    )
    nil ;
) )

(def (vec-head ve n) ;
  (letn ([ret (mk-vec n)])
    (for [i n]
      (vec-set-fnum! ret i [vec-ref ve i]) )
    ret
) )

(def (vec-tail ve m)
  (letn ([n (-(vec-len ve)m)][ret (mk-vec n)])
    (for [i n]
      (vec-set-fnum! ret i [vec-ref ve [+ m i]]) )
    ret
) )
(def vec-cdr (rcurry vec-tail 1)) ;@
(defn vec-dmap (g xs) ;
  (def [_ xs]
    (if [vec-nilp xs] vnil
      (let ([a (vecar xs)][d (vecdr xs)]) ;
        (if (vec-consp a) ;
          [vecons [_ a] [_ d]] ;flat & bump/hunch
          [vecons (g a) [_ d]]
  ) ) ) )
  [_ xs]
)

; (def (vec-foldl g x ve) ;walker? ref nilp
  ; (vec-for y in ve ;
    ; [set! x (g x y)] ) ;tmp ;(_ g tmp ve) try
  ; x
; )
(def (vec-foldl g x ve)
  (let ([n (vec-len ve)])
    (def (_ ret i)
      (if (>= i n) ret
        (let ([y (vec-ref ve i)]) ;try is slow
          [_ (g ret y) (1+ i)]
    ) ) )
    (_ x 0)
) )

(def (vec-redu g ve) ;slower than redu
  ;(vec-foldl g (vec-car ve) (vec-cdr ve)) ;
  (redu g (vec->lis ve))
)

(def (vec-swap! ve i j) ;!
  (let ([t 0])
    (set! t (vec-ref ve i))
    (vec-set-fnum! ve i (vec-ref ve j))
    (vec-set-fnum! ve j t)
) )

(def (vec-rev! ve)
  (letn ([n (vec-len ve)] [m (1- n)] [h (quot n 2)])
    (for (i h)
      (vec-swap! ve i [- m i])
) ) )

(def vec-copy! ;
  (case-lam
    [(ve) (vec-copy ve)]
    [(des i) (vec-tail des i)]
    [(des i src)
      [vec-copy! des i src (vec-len src)] ] ;
    [(des i src n)
      (letn ([dn (vec-len des)][m (min n [- dn i])])
        (for (j m)
          (vec-set! des (+ i j) (vec-ref src j)) ) ) ]
) )

(def (vec-append . vz)
  (letn ([n (len vz)][ns (map vec-len vz)][ret (mk-vec [redu + ns])])
    (for (i n)
      (vec-copy! ret (redu + [head ns i]) (xth vz i)) )
    ret
) )


;algo for vec-sort

; sort

(def (car->end! xs) ;end->car! 1
  (if (cdr-nilp xs) xs ;
    (bgn
      (set-cdr! (last-pair xs) (list (car xs))) ;
      (set-car! xs (cadr xs)) ;
      (set-cdr! xs (cddr xs)) ;
      xs
) ) )


(def qsort
  (case-lam
    ([xs f] (sort f xs ))
    ([xs]   (qsort xs <))
) )

; (dont-return!) (setq a (rand-seq (range 1000000)))
; (elap (mysort a)) (elap (qsort a fx>)) (elap (msort a fx>))
(def/va (mysort xs [g fx>]) ;2~@ than qsort when rand
  (def (~ xs ret)
    (if (nilp xs) ret
      (letn
        ( [a   (car xs)]
          [lr  (filter2 (lam (x) [g x a]) (cdr xs))] ;
          [pre (car  lr)]
          [pos (cadr lr)] )
        [~ pre (cons a [~ pos ret])] ;
  ) ) )
  (~ xs nil)
)

(ali msort merge-sort) ;msort/f [id] ;sort-by-comp
(def (merge-sort ls <?) ;lt? ;2x+ slower than sort
  (def (merge~ xs ys)
    (if (nilp xs) ys
      (if (nilp ys) xs
        (if [<? (car xs) (car ys)]
          (cons [car xs] [merge~ (cdr xs) ys]) ;
          (cons [car ys] [merge~ xs (cdr ys)])
  ) ) ) )
  (def [_ ls n]
    (if (fx< n 2) ls
      (let ([mid (quotient n 2)])
        (merge~
          [_ (head ls mid) mid]
          [_ (tail ls mid) (fx- n mid)]
  ) ) ) )
  [_ ls (len ls)]
)

(def/va (sort-by-sames xs [g >] [h >] [append? T]) ;>/</nil
  (letn
    ( [pre (if [nilp g] xs (qsort xs g))]
      [tmp (compress pre)]
      (next
        (if [nilp h] tmp
          (qsort tmp
            [lam (x y) (h (cadr x) (cadr y))]
    ) ) ) )
    (decompress next append?)
) )

(def randnums
  (case-lam
    ([n s e] ;e-s+1 + s ;range?
      (let ([m (- (1+ e) s)])
        (def (_ ret n)
          (if (fx< n 1) ret
            [_ (cons [+ s (random m)] ret) (fx1- n)] ;
        ) )
        (_ nil n)
    ) )
    ([n m]
      (def (_ ret n)
        (if (fx< n 1) ret
          [_ (cons (random m) ret) (fx1- n)] ;
      ) )
      (_ nil n)
    )
    ([n] [randnums n n])
) )

; doc 2 for documentable

(def/va (docs-main [ht (if (htab/fn-lam?) *htab/fn-lam* *htab/fn-doc*)]) ;
  ht
)
(def/va (docs [ht (if (htab/fn-lam?) *htab/fn-lam* *htab/fn-doc*)])
  (map
    (lam (k)
      (cons k
        (ev `(doc-paras ,k)) ;
    ) )
    (map car ht)
) )

; htab 2 for hashtable

(def (htab/key-exist? key ht)
  (def (_ ht)
    (if (nilp ht) F
      (if (eq key (caar ht)) T
        [_ (cdr ht)]
  ) ) )
  (_ ht)
)

(def (doc% ht key) ;not htab-value
  (def (_ ht)
    (if (nilp ht) nil
      (if (eq key (caar ht))
        (let ([tmp (cadar ht)]) ;
          (if (str? tmp) tmp ;?
            (car ht)
        ) )
        [_ (cdr ht)]
  ) ) )
  (_ ht)
)
(def (doc-paras% ht key)
  (def (_ ht)
    (if (nilp ht) nil
      (if (eq key (caar ht))
        (let ([val (cadar ht)]) ;
          (if (consp val)
            (if [eq 'lam (car val)]
              ;[sym/with-head? (car val) 'lam] ;@
              (cadr val)
              nil )
            nil
        ) )
        [_ (cdr ht)]
  ) ) )
  (_ ht)
)

(def (htab-value ht key)
  (def (_ ht)
    (if (nilp ht) nil
      (if (eq key (caar ht))
        (cadar ht)
        [_ (cdr ht)]
  ) ) )
  (_ ht)
)
(def (htab-kv ht key)
  (def (_ ht)
    (if (nilp ht) nil
      (if (eq key (caar ht))
        (car ht)
        [_ (cdr ht)]
  ) ) )
  (_ ht)
)
(def (htab-kvs htab key-with)
  (filter
    (compose (rcurry with?-nocase key-with) car)
    htab
) )
(def (htab-keys htab key-with)
  (filter
    (rcurry with?-nocase key-with) ;
    (map car htab)
) )
(def (htab-values htab key-with)
  (map ;
    cadr
    (filter ;todo new filter-with-action
      (compose (rcurry with?-nocase key-with) car)
      htab
) ) )
;(find-htab-key htab value  [eql])
;(find-htab-keys htab value [eql])

; logic

(def_ [exist-cond? g x xs] ;
  (if (nilp xs) F ;
    (let/ad xs
      (if (g x a) T
        [_ g x d]
) ) ) )

(def_ [exist-relation?/adjacent g xs] ;
  (if (nilp xs) F
    (letn
      ([d (cdr xs)] [b (exist-cond? g (car xs) d)])
      (if b T
        [_ g d]
) ) ) )

;(alias defnest defn-nest)

(def (exist-match? g xs)
  (def (_ xs)
    (if~
      [nilp xs]
        F
      [g (car xs)]
        T ;
      [_ (cdr xs)]
  ) )
  (_ xs)
)

;(_ (lam (x) (cn-char? x)) '((#\我) #\3))
(def (deep-exist-match? g xs)
  (def (_ x flg)
    (if~
      [nilp  x] flg
      [consp x]
        (_ (car x)
          [_ (cdr x) flg] )
      (if (g x) T
        flg
  ) ) )
  (_ xs F)
)

;issue: if multi same keys/kvs
;(x-is-y? 'Jack 'will-die '([Jack human][human will-die]))
(def/va (x=>y? x y [xys '([x a][a y])] [defa nil])
  (def (~ k)
    (if [eq k y] T
      (let ([tmp (key->val xys k eq id T defa)]) ;
        (if [eq tmp defa] F ;
          [~ tmp]
  ) ) ) )
  (~ x)
)

;todo: Dijkstra

; (defun memorize (fn) ;f.xs
  ; (let ([cache (make-hash-table :test eql)]) ;
    ; (lambda args
      ; (multiple-value-bind (val win) (gethash args cache) ;
        ; (if win val
          ; (setf (gethash args cache) ;
            ; (apply fn args)
; ) ) ) ) ) )

(def (memorized-fx proc) ;
  (let ([cache nil]) ;
    (lam (x) ;
      (cond ;([assq x cache] => cdr) ;(cdr resl)
        ([key->kv cache x eql T F] => cdr) ;
        (else
          (let ([ans (proc x)])
            (set! cache [cons (cons x ans) cache]) ;just para and answer in cache for this fx
            ans
) ) ) ) ) )

;;; standard prelude @

; list utilities


(def (rand-elem xs) ;~> x
  [xth xs (random (len xs))] ;@
)

;(divide-after '(x m k y) '(m k)) ;~> '([x m k] [y])
(def (divide-after xs mark)
  (def (_ ret tmp xs ys)
    (if [nilp xs] ;atomp
      (cons tmp ret)
      (if (nilp ys)
        [_ (cons tmp ret) nil xs mark]
        (let ([ax (car xs)] [ay (car ys)] [dx (cdr xs)] [dy (cdr ys)])
          (if (eq ax ay)
            [_ ret (cons ax tmp) dx dy]
            [_ ret (cons ax tmp) dx mark]
  ) ) ) ) )
  [deep-rev (_ nil nil xs mark)]
)

;aas
;(divide-before (str->list "1asdsadas") (str->list "as"))
(def (divide-before xs MARK)
  (def (_ ret tmp tmp1 xs ys flg) ;flg for eq
    (if~
      [nilp xs] ;atomp
        (if (nilp ys)
          (cons* tmp1 (redu append tmp) ret)
          (cons (append tmp1 tmp) ret) ) ;@?
      (nilp ys) ;flg ;
        [_ (cons (redu append tmp) ret) nil tmp1 xs MARK F] ;
      (let ([ax (car xs)] [ay (car ys)] [dx (cdr xs)] [dy (cdr ys)])
        (if (eq ax ay)
          (if flg
            [_ ret tmp (cons ax tmp1) dx dy T]
            [_ ret (cons tmp1 tmp) (cons ax nil) dx dy T] )
          (if flg
            [_ ret tmp tmp1 xs MARK F]
            [_ ret tmp (cons ax tmp1) dx MARK F]
  ) ) ) ) )
  [deep-rev (_ nil nil nil xs MARK F)]
)

(def (divide-before-if xs g) ;-if
  (def (_ ret tmp xs)
    (if~
      (nilp xs) ;atomp
        (cons tmp ret) ;
      (let/ad xs
        (if (g a) ;tmp
          (if (nilp tmp)
            [_ ret (list a) d]
            [_ (cons tmp ret) (list a) d] )
          [_ ret (cons a tmp) d]
  ) ) ) )
  [deep-rev (_ nil nil xs)] ;
)

;(divide '(x y m k) '(m k))
;(divide '(x m k m y m k z o) '(m k)) ;~> '([x] [m y] [z o])
;seps: (divides '(x m k m o y m k z o) '[(m k) (o)]) ;~> '([x][m][y][z][])
(def (divide xs sep)
  (def (_ ret elem tmp xs ys) ;
    (if~
      (nilp ys)
        [_ (cons elem ret) nil nil xs sep]
      (nilp xs) ;atomp
        (cons (append tmp elem) ret) ;~append
      (let ([ax (car xs)] [dx (cdr xs)] [ay (car ys)] [dy (cdr ys)]) ;
        (if (eq ax ay) ;
          [_ ret elem (cons ax tmp) dx dy] ;
          [_ ret (cons ax (append tmp elem)) nil dx sep]
  ) ) ) )
  [deep-rev (_ nil nil nil xs sep)] ;
)

;(divide-at (str->list "asd") 1 2) ~> '([#\a]..)
(def (divide-at xs i) ;[pos 'after]
  (def (_ ret xs j)
    (if (nilp xs)
      (list ret nil) ;rev
      (if (eq j i) ;
        (list ret xs) ;rev
        [_ (cons (car xs) ret) (cdr xs) (1+ j)]
  ) ) )
  (_ nil xs 0)
)

;(filter-nths (curry eq 5) '(1 123  5 654 6 5 2)) ;-> nths
(def (filter-nths g xs)
  (def (~ nths i xs)
    (if [nilp xs] nths
      (let/ad xs
        (if [g a]
          [~ (cons i nths) (1+ i) d]
          [~ nths (1+ i) d]
  ) ) ) )
  (~ nil 1 xs) ;
)

(define (split n xs)
  (let loop ((n n) (xs xs) (zs '()))
    (if (or (zero? n) (null? xs))
        (values (reverse zs) xs)
        (loop (- n 1) (cdr xs) (cons (car xs) zs)))))

(define (take-while pred? xs)
  (let loop ((xs xs) (ys '()))
    (if (or (null? xs) (not (pred? (car xs))))
        (reverse ys)
        (loop (cdr xs) (cons (car xs) ys)))))

(define (drop-while pred? xs)
  (let loop ((xs xs))
    (if (or (null? xs) (not (pred? (car xs)))) xs
      (loop (cdr xs)))))

(define (split-while pred? xs)
  (let loop ((xs xs) (ys '()))
    (if (or (null? xs) (not (pred? (car xs))))
        (values (reverse ys) xs)
        (loop (cdr xs) (cons (car xs) ys)))))

;;

(defn call-nest (g . xs) ;
  (defn ~ (g xs)
    (if (nilp xs) (g)
      (~ (g (car xs)) (cdr xs))
  ) )
  (~ g xs)
)

(defn call-snest (g . ys)
  (defn ~ (g ys)
    (if (nilp ys) g
      [~ (g (car ys)) (cdr ys)]
  ) )
  (~ g ys)
)

;

(load-lib "kernel32.dll") ;Beep
(defc* GetCommandLineA () string get-command-line)
(defc c-beep (freq dura) void* Beep (void* void*))
(defc c-sleep (ms) unsigned Sleep (unsigned) __collect_safe) ;(defc c-sleep Sleep 1) ;(ms) ;__collect_safe "sleep"

(load-lib "shell32.dll")
(def-ffi shell-execute (ShellExecuteA (int string string string string int)))

(load-lib "msvcrt.dll")
(defc void* clock ())

(load-lib "winmm.dll")
(defc midi-out-get-num-devs() int midiOutGetNumDevs()) ;
;
;(def-ffi (midi-connect dev) (void* midiConnect (void*)) "comment/body: ret bool")
;midiConnect (HMIDI hmi, HMIDIOUT hmo, LPVOID pReserved)
;BOOL sndPlaySound (LPCSTR lpszSound, UINT fuSound);

;(def (main-args) (str-split (GetCommandLineA) spc))

(def CLOCKS_PER_SEC 1000)
(setq SW_MINIMIZE 6)

;---

(def (sleep ms) (c-sleep [fixnum ms])) ;sleep

(def/va (beep [freq 456] [dura 188]) (c-beep freq dura))

(def (clock*)
  (inexact (/ (clock) CLOCKS_PER_SEC)) ;
)

(def (get-ms) ;get-sec-nano
  (letn
    ( [time (current-time)] ;
      [sec  (time-second time)]
      [nano (time-nanosecond time)] )
    [+ (* sec [pow 10. 3.]) (* nano [pow 10. -6.])] ;(real-time)?
    ;(list sec nano)
) )

(def (eq/eql x) ;
  (if (str/pair/vec? x)
    eql eq
    ; (if (num? x)
      ; = ;
      ; eq )
) )

;(def (mem?% x xs) (bool (mem? x xs)))

(def/va (mem?% x xs [= eql] [get id] [ret id])
  (def (_ xs)
    (if [nilp xs] F
      (let/ad xs
        (if
          [= x [get a]]
            (cons [ret a] d)
          [_ d]
  ) ) ) )
  (_ xs)
)

;(setq a '(1 2 2 3 3 3 4)) ;~> '(2 3)
(def (filter-same xs)   ;OK ;exist-same?
  (def (_ xs pure same) ;curr .vs. 1.pure, 2.same -> 3.ign
    (if (nilp xs) same  ;return
      (let ([a (car xs)])
        (if (mem? a pure)          ;1
          (if (mem? a same)        ;2 ;
            [_ (cdr xs) pure same] ;3
            [_ (cdr xs) pure (cons a same)] )
          [_ (cdr xs) (cons a pure) same] ;
  ) ) ) )
  [_ xs nil nil] ;rev ;final handling
)

(def (exist-same? xs )
  (def (_ xs pure)
    (if (nilp xs) F
      (let ([a (car xs)])
        (if (mem? a pure) T ;
          [_ (cdr xs) (cons a pure)]
  ) ) ) )
  [_ xs nil]
)

(def (remov-same xs) ;filter-pure
  (def (_ xs ts)
    (if (nilp xs) ts
      (let ([a (car xs)])
        (if (mem? a ts) ;
          [_ (cdr xs) ts]
          [_ (cdr xs) (cons a ts)] ;
  ) ) ) )
  (rev [_ xs nil]) ;
)

;yin's code

(def cps ;cont-pass-style ;
  (lam (exp) ;lam-quote-exp: nontailrec->tailrec
    (letrec ;recurse
      ( [trivial? ;
          (lam (x) ;
            (memq x '(zero? add1 sub1)) )] ;member-quo?
        [ctx0 (lambda (v) `(k ,v))]      ; tail context
        (fv ;
          (let ([n -1])
            (lam ()
              (set! n (1+ n))
              (string->symbol (string-append "v" (number->string n))) ) ) )
        (cps1 (lam (exp ctx)
            (pmatch exp ;
              ( ,x [guard (not (pair? x))] (ctx x) )
              ( [if ,test ,conseq ,alt]
                (cps1 test (lam (t)
                    (cond
                      [(memq ctx (list ctx0 id))
                       `(if ,t ,(cps1 conseq ctx) ,(cps1 alt ctx))]
                      (else
                        (let ([u (fv)])
                         `(let ([k (lambda (,u) ,(ctx u))])
                            (if ,t ,(cps1 conseq ctx0) ,(cps1 alt ctx0))
              ) ) ) ) ) ) )
              ( [lam (,x) ,body]
                (ctx `(lambda (,x k) ,(cps1 body ctx0))) )
              ( [,op ,a ,b]
                (cps1 a (lam (v1)
                    (cps1 b (lam (v2)
                        (ctx `(,op ,v1 ,v2))
              ) ) ) ) )
              ( [,rator ,rand]
                (cps1 rator (lam (r)
                    (cps1 rand (lam (d)
                        (cond
                          [(trivial? r)    (ctx `(,r ,d))]
                          [(eq? ctx ctx0) `(,r ,d k)]  ; tail call
                          (else
                            (let ([u (fv)])
                             `(,r ,d (lam (,u) ,(ctx u)))
      ) ) ) ) ) ) ) ) ) ) ) )
      (cps1 exp id)
) ) )

;to-test: https://blog.csdn.net/lifan_3a/article/details/41677801

(def (rec-chk n f x0 . xs0) ; ;(_ 20 + 0 1 2)
  (def (_ x m)
    (if (>= m n) x ;
      [_ (redu f (cons x xs0)) (1+ m)] ;recurse
  ) )
  (_ x0 0)
)

(def (fix-chk n f . xs) ;to help improve speed
  (def (_ x n)
    (if (fx< n 1) x ;
      (_ (apply f xs) (fx1- n)) ;
  ) )
  (_ nil n)
)

(def with-head?
  (case-lam
    ( [xs ys eql] ;(_ '(1 2 3 4) '(1 2/3)) ;-> Y/N
      (def (_ xs ys)
        (if~
          (nilp ys) xs ;T
          (nilp xs) F
          (eql (car xs) (car ys))
            [_ (cdr xs) (cdr ys)]
          F
      ) )
      (_ xs ys))
    ( [xs ys]
      (with-head? xs ys eql)
) ) )
(def with? ;may need algo
  (case-lam
    ( [xs ys eql] ;(_ '(1 2 3 4) '(2 3/4)) ;-> Y/N ;with/contain-p
      (def (_ xs)
        (if (nilp xs) F
          (let ([tmp (with-head? xs ys eql)])
            (if tmp tmp ;T
              [_ (cdr xs)] ;
      ) ) ) )
      (if (nilp ys) F
        (_ xs)
    ) )
    ( [xs ys]
      (with? xs ys eql)
) ) )
;(withs? (str->list "asdf") (map str->list '("as" "f")))
(def (withs? xs yz)
  (def (~ xs yz)
    (if (nilp yz) T
      (let/ad* yz ([rest (with? xs a)])
        (if rest [~ rest d] F)
  ) ) )
  (~ xs yz)
)

(def/doc (with-sym? s x) ;sym/with?
  (redu (rcurry with? eq) ;
    (map (compose str->list sym->str) ;str-downcase
      (list s x) ;
) ) )
(def/doc (with?-nocase s x)
  (redu (rcurry with? eq) ;
    (map (compose str->list str-downcase str) ;any<-sym
      (list s x) ;
) ) )
(def/doc (sym/with-head? s x)
  (redu (rcurry with-head? eq) ;
    (map (compose str->list sym->str) ;
      (list s x) ;
) ) )

(def (syms) (environment-symbols (interaction-environment)))

;

;num2lis num2abc abc2num

(def (repeats xs n) ;ng
  (redu (curry map li) (xn->list xs n))
  ; (redu (curry map-all list)
    ; (nx->list n xs) )
)

;unify -- onlisp?

(def_ (contain. e m)
  (if~
    (nilp e) F
    (atom e) (eql e m) ;
    (if~
      [_ (car e) m] T
      [_ (cdr e) m] T
      F
) ) )
(def_ (sb. e s1) ;exp symbols
  (if~
    [nilp e] nil
    [atom e] (if [eql e (cadr s1)] (car s1) e) ;
    (let ([head. [_ (car e) s1]] [tail. [_ (cdr e) s1]])
      (cons head. tail.) ;
) ) )
(def (substitution. e m)	;~置换 exp marks
  (def (~ e m)
    (if (nilp m) e
      [~ (sb. e (car m)) (cdr m)] ;
  ) )
  (~ e m)
)
(def (compose. s1 s2)
  (def (_cp s1 s2)
    (if [nilp s1] nil
      (letn ([ti(caar s1)] [vi(cdar s1)] [new_ti(substitution. ti s2)])
        (cons (cons new_ti vi) [_cp (cdr s1) s2])
  ) ) )
  (append (_cp s1 s2) s2)
)

(def/va (unify e1 e2 [syms '(x y)]) ;(unify '(a b) '(x y) '[x y])
  (def (~ e1 e2)
    (let ([bf 0] [f1 0][f2 0] [t1 0][t2 0] [s1 0][s2 0] [g1 0][g2 0]) ;
      (cond
        ( [or (atom e1) (atom e2)]
          (when [not (atom e1)] (setq  bf e1  e1 e2  e2 bf)) ;
          (cond
            ((equal e1 e2)                         nil) ;
            ([and (mem? e1 syms) (contain. e2 e1)] 'fail) ;
            ; ((mem? e1 syms)                        `[,(list e2 e1)]) ;
            ; ((mem? e2 syms)                        `[,(list e1 e2)])
            ((mem? e1 syms)                        `(,[list e1 e2])) ;
            ((mem? e2 syms)                        `(,[list e2 e1]))
            (else                                  'fail)
        ) )
        (else
          (setq
            f1 (car e1)   t1 (cdr e1)
            f2 (car e2)   t2 (cdr e2)
            s1 [~ f1 f2] )
          (cond
            ([eq s1 'fail] 'fail)
            (else
              (setq g1 (substitution. t1 s1))
              (setq g2 (substitution. t2 s1))
              (setq s2 [~ g1 g2])
              (if [eq s2 'fail] 'fail (compose. s1 s2))
  ) ) ) ) ) )
  (~ e1 e2)
) ;type infer

;(unify '(p a b) '(p x y) '[x y]) ;~> ((A X) (B Y))
;(unify '[x(f x)(g z)] '[y (f(g b)) y] '(x y z))
;(unify `(a b) `(b X) '(X)) ;?-> fail

(def (sym->chs sym)
  (str->list (sym->str sym))
)
(def (chs->sym chs)
  (str->sym (list->str chs))
)

; data

(def/va (data-compress xs [chk? F]) ;for simply compressing pic data
  (let ([tmp (compress (qsort xs))]) ;qsort more>less
    (if (and chk? [> (len tmp) (sqrt (1+ (redu max xs)))]) xs ;.1+
      (letn
        ( [vals (map car tmp)]
          [kv   (list/nth vals 0)] ;
          [keys (map (lam (v) (val->key kv v)) xs)] )
        (list kv keys)
) ) ) )

(def/va (data-size/bits dat [nbits 1])
  (letn
    ( [mx (1+ (redu max dat))] ;1+ ;
      [mx-bit (ceil (log mx 2))] ;.
      [ln (len dat)] )
    (./ (* mx-bit ln) nbits) ;
) )

(def (data-decompress kv-keys) ;if
  (letn
    ( [keys (cadr kv-keys)]
      [kv   (car  kv-keys)]
      [vals (map (lam (k) (key->val kv k)) keys)] )
    vals
) )

;(rgb->yuv '(r g b)) ;-> '(y u v)
(def (rgb->yuv rgb) ;std ;601/std/709 
  (let
    ( [y (foldl +  0  (map * '( 0.29882   0.58681   0.114363) rgb))] ;std
      [u (foldl + 128 (map * '(-0.172485 -0.338718  0.511207) rgb))] ;Pb
      [v (foldl + 128 (map * '( 0.51155  -0.42811  -0.08343 ) rgb))] ;Pr
    )
    (map int (list y u v)) ;
) )

;(yuv->rgb (rgb->yuv '(255 127 63)))
(def (yuv->rgb yuv)
  (letn
    ( [y (car yuv)] [u (- (cadr yuv) 128)] [v (- (caddr yuv) 128)] ;
      [r (+ y (* 1.370705 v))] ;std
      [g (+ y (* -0.337633 u) (* -0.698001 v))]
      [b (+ y (* 1.732446 u))]      
    )
    (map int (list r g b)) ;
) )

(setq *tab/jp/key-a-A* ;Xy: y: a i u e o ;z: n
 '( [  a あ ア][  i い イ][  u う ウ][  e え エ][  o お オ] ;ェ
    [ ka か カ][ ki き キ][ ku く ク][ ke け ケ][ ko こ コ]
    [ sa さ サ][shi し シ][ su す ス][ se せ セ][ so そ ソ]
    [ ta た タ][chi ち チ][tsu つ ツ][ te て テ][ to と ト]
    [ na な ナ][ ni に ニ][ nu ぬ ヌ][ ne ね ネ][ no の ノ]
    [ ha は ハ][ hi ひ ヒ][ fu ふ フ][ he へ ヘ][ ho ほ ホ] ;*
    [ ma ま マ][ mi み ミ][ mu む ム][ me め メ][ mo も モ] ;* mu
    [ ya や ヤ][ yi い イ][ yu ゆ ユ][ ye え エ][ yo よ ヨ] ;-i e
    [ ra ら ラ][ ri り リ][ ru る ル][ re れ レ][ ro ろ ロ] ;*
    [ wa わ ワ][ wi い イ][ wu う ウ][ we え エ][ wo を ヲ] ;-i u e ;* wo
    [  n ん ン]
    [ ga が ガ][ gi ぎ ギ][ gu ぐ グ][ ge げ ゲ][ go ご ゴ]
    [ za ざ ザ][ zi じ ジ][ zu ず ズ][ ze ぜ ゼ][ zo ぞ ゾ] ;
    [ da だ ダ][ di ぢ ヂ][ du づ ヅ][ de で デ][ do ど ド]
    [ ba ば バ][ bi び ビ][ bu ぶ ブ][ be べ ベ][ bo ぼ ボ]
    [ pa ぱ パ][ pi ぴ ピ][ pu ぷ プ][ pe ぺ ペ][ po ぽ ポ] ;
    ;--- extra
    [ si し シ]
    [ ti ち チ][ tu つ ツ][chu つ ツ]
    [ hu ふ フ]
    [ ji じ ジ]
) )

;doremi-hz
(setq *doremi-hz* ;[pow 2 1/12] ~< 1.06
  '(
    ;# : do2 re2, ...
    ;_.: do. re., fa. so. la.
    ;._: .re .mi, ...
    ;(256 271 287 304 323 342 362 384 406 431 456 483 512) ;Hz
    256.0 271.2 287.4 304.4 322.5 341.7 362.0 383.6 406.4 430.5 456.1 483.3 ;flo
    ;[256.0  287.4  322.5 341.7  383.6  430.5  483.3]
) )

(setq
  Mu  1 ;~ > Mute
  Do  [nth *doremi-hz*  1]
  Do2 [nth *doremi-hz*  2]
  Re  [nth *doremi-hz*  3]
  Re2 [nth *doremi-hz*  4]
  Mi  [nth *doremi-hz*  5]
  Fa  [nth *doremi-hz*  6]
  Fa2 [nth *doremi-hz*  7]
  So  [nth *doremi-hz*  8]
  So2 [nth *doremi-hz*  9]
  La  [nth *doremi-hz* 10]
  La2 [nth *doremi-hz* 11]
  Si  [nth *doremi-hz* 12] )
(setq
  .Do  [(rcurry / 2) Do ]    Do.  [(curry * 2) Do ]
  .Do2 [(rcurry / 2) Do2]    Do2. [(curry * 2) Do2]
  .Re  [(rcurry / 2) Re ]    Re.  [(curry * 2) Re ]
  .Re2 [(rcurry / 2) Re2]    Re2. [(curry * 2) Re2]
  .Mi  [(rcurry / 2) Mi ]    Mi.  [(curry * 2) Mi ]
  .Fa  [(rcurry / 2) Fa ]    Fa.  [(curry * 2) Fa ]
  .Fa2 [(rcurry / 2) Fa2]    Fa2. [(curry * 2) Fa2]
  .So  [(rcurry / 2) So ]    So.  [(curry * 2) So ]
  .So2 [(rcurry / 2) So2]    So2. [(curry * 2) So2]
  .La  [(rcurry / 2) La ]    La.  [(curry * 2) La ]
  .La2 [(rcurry / 2) La2]    La2. [(curry * 2) La2]
  .Si  [(rcurry / 2) Si ]    Si.  [(curry * 2) Si ] )

; logic for data

(def (jp/prono-divide prono) ;pronounce: hi ra ga na->ひらがな ;saranghae X:gha
  (let
    ( [vowels '(#\a #\i #\u #\e #\o)]
      [spec  #\n] ) ;
    (def (~ cs ret tmp flg) ;aft-n
      (if (nilp cs)
        (cons tmp ret)
        (letn
          ( [a (car cs)] [d (cdr cs)]
            [a.tmp (cons a tmp)] ) ;
          (if~
            (mem? a vowels)
              [~ d (cons a.tmp ret) nil F]
            flg
              [~ d (cons tmp ret) (cons a nil) F]
            (eq a spec)
              [~ d ret a.tmp T]
            [~ d ret a.tmp F]
    ) ) ) )
    (map chs->sym
      (deep-reverse [~ (sym->chs prono) nil nil F]) ;
) ) )

(def (doremi->Hz one)
  (let ([mapp (list Do Do2 Re Re2 Mi Fa Fa2 So So2 La La2 Si)]) ;
    (nth mapp one)
) )

(def/va (play-hz [freq 456] [ms 200]) ;[scale-offs 0]) ;pow 2 scale-offs
  (beep [int freq] ms)
)

(def/va (play-hzs hzs [ms 200] [freq? T])
  (let ([conv (if freq? id doremi->Hz)])
    (for-each ;
      (lam [x]
        (play-hz [conv x] ms) ) ;
      hzs ;mss
    ) T
) )

; settings

; setq global vars

(setq *paths* nil) ;shared ;ng name ;*choose-paths*

(setq
  *chs-numbers*  [map digit->char (myrange 0 9)] ;
  *chs-Letters*  (str->list "ABCDEFGHIJKLMNOPQRSTUVWXYZ") ;A~H 8
  *chs-letters*  (map char-downcase *chs-Letters*)
  *syms-numbers* (myrange 0 9)
  *syms-Letters* (map [flow char->string str->sym] *chs-Letters*)
)

(setq *current-path* (cd)) ; ?"Pro File"

; (def car car%) ;
; (def cdr cdr%)
; (def cadr (compose car cdr))
; (def cddr (compose cdr cdr))
;cddddr

; how to refine?
(set! *script-path* ;%
  (let
    ( [tmp
        (remove "" ;
          (string-divide (get-command-line) " ")
    ) ] )
    (if (cdr-nilp tmp)
      ".\\" ;
      (car (string->path-file ;
          (car (remove ""
              (string-divide
                (cadr tmp) ;
                "\""
) ) ) ) ) ) ) ) ;bug if just use load

(define (load-relatived file) ;cd
  (load
    (string-append *script-path* ;
      [(if (sym? file) symbol->string id) file]
) ) )

; --- doc ---

(doc-add '(load-lib "x.dll"))

; ======

(def (restore)
  (setq
    nil nil
    ; car #3%car
    ; cdr #3%cdr
    ; map #3%map
    ; +   #3%+
) )
