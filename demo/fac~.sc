
;fac~: 4x faster then the tail rec edition of the fac func

;chez chez-lib.sc {self}.sc
;mychez {self}.sc
;(load "c:/path/to/chez-lib/lib.sc")

;--

;(fac~ 5w) ;~ 1644->664->484->424 ms

(def (fac~ n) ;~ n>=1 ;gmp/hugeCalc
  (def (calc rets)
    (letn
      ( [odd  (redu * (~odds rets))] ;
        [rest (cdr rets)]
        [gps  (map (curry redu *) (group rest 2))] ) ;
      (def (~ xs)
        (if [nilp xs] 1
          (let/ad xs
            (pow (* [~ d] a)) ;
      ) ) )
      (* odd [~ gps])
  ) )
  (def/va (F2 f [e -1])
    (redu * (range f [fx+ 2 e] fx- 2)) ;
  )
  (def (f1~ mm n kk) ;(F1 f [e 0]) -> (F1 f e)(F1 e d)..
    (case n
      ([1 2] ;
        (* n
          [calc (do-for-pairs (append/rev-head mm '(-1)) F2)] ;
          (pow 2 kk) ;
      ) )
      (else
        (letn
          ( [b   (fxeven? n)]
            [n-1 (fx1- n)]
            [m   (if b n-1 n)]
            [2k  (if b n n-1)]
            [k   (>> 2k 1)] )
          [f1~ (cons m mm) k (fx+ kk k)] ;
  ) ) ) )
  (f1~ nil n 0)
)

;(load (str *lib-path* "demo/fac~.sc"))

;(elapse (fac~ 50000))
;(eql (fac~ 50000) (fac 50000))
