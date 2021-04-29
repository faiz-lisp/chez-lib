
;Generate code for your input, output

;chez chez-lib.sc {self}.sc
;mychez {self}.sc
;(load "c:/path/to/chez-lib/lib.sc")

;--

(def (null . paras)
  nil
)

(def (id-last . xs)
  (last xs)
)

;--

(def (form-f8 fs)
  (let
    ( [f (nth fs 1)]
      [g (nth fs 2)]
      [h (nth fs 3)]
      [i (nth fs 4)]
      [j (nth fs 5)]
      [k (nth fs 6)]
      [l (nth fs 7)]
      [m (nth fs 8)] )
    `(lam (x)
      (def [~ ret x] ;self
        (if [,g (,f x)] ;nilp consp atomp ;(nth fs n)
          (,j (,i ret) (,h x)) ;(g ret) ;id null rev
          [~ (,m (,l x) ret) (,k x)] ;cdr car cons ;
      ) )
      (~ nil x)    
) ) )

(def (form-f10 fs)
  (let
    ( [f (nth fs 1)]
      [g (nth fs 2)]
      [h (nth fs 3)]
      [i (nth fs 4)]
      [j (nth fs 5)]
      [k (nth fs 6)]
      [l (nth fs 7)]
      [m (nth fs 8)]
      [n (nth fs 9)]
      [o (nth fs 10)] )
    `(lam (xz) ;'((w x)(y z)) -> '(w x y z) ;'((y z)(x w)) -> '(w x y z)
      (def (~ ret x) ;last rev
        (if (,i (,h x))
          (,l (,k ret) (,j x))
          (~ (,o (,n x) ret) (,m x))
      ) )
      (~ (,f xz) (,g xz)) ;
) ) )

(def
  (f8 f g
    h i j
    k l m ) ;. paras) ;f-x main
  (lam (x)
    (def [~ ret x] ;self
      (if [g (f x)] ;nilp consp atomp ;(nth fs n)
        (j (i ret) (h x)) ;(g ret) ;id null rev
        [~ (m (l x) ret) (k x)] ;cdr car cons ;
    ) )
    (~ nil x)
) )

(def (f10  f g h i j  k l m n o)
  (lam (xz) ;'((w x)(y z)) -> '(w x y z) ;'((y z)(x w)) -> '(w x y z)
    (def (~ ret x) ;last rev
      (if (i (h x))
        (l (k ret) (j x))
        (~ (o (n x) ret) (m x))
    ) )
    (~ (f xz) (g xz)) ;(rev (g xz))
) ) ;car cadr cdr nilp car id-last cons

;(code-for '(a b) '(b a))
(def/va
  (code-for in out  [fx f8] [n-fns 8] [= eql] ;[data '(F nil T 0 1)] ;[ops '(nilp consp atomp id null rev cdr car cons)]
    [form-fx form-f8]
    ;cons car cdr nilp  null id-last  id rev last  0 1 1+
    [ops `(id id-last null  nilp cdr car cons)] ) ;(cons x)?
    ;[ops `(null  car cadr cdr nilp car id-last cons)] ) ;?
    ;[ops `(id null  car cadr cdr nilp car id-last cons)] )
  (clean-choose)
  (letn
    ( ;[data (rand-seq data)] ;
      [op-syms (rev ops)] ;!
      [ops     (map ev  op-syms)] ;!
      [op-mapp (zip ops op-syms)]
      [show    (curry map (curry key->val op-mapp))]
      [fs   (chooses ops n-fns T)] ;!
      (main (redu fx fs)) ;!
      ;[resl (try (= out (main main nil in)))] ;?
      [resl (try (= out (main in)))] ;?
      [bool (if (try-fail? resl) F resl)] )
    (if bool ;(show fs)
      (form-fx (show fs)) ;
      [fail] ;fail-and-goon
) ) )

;(cost (code-for '(1 2) '2))     ;150 ms
;(cost (code-for '(1 2) '(2 1))) ;150 ms
;(cost (code-for '(1 2) '2 f10 10 eq form-f10)) ;800 ms
;(cost (code-for '(1 2) '(2 1) f10 10 eql form-f10)) ;12 s
