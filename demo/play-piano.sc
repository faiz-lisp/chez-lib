
; Play piano with Windows API Beep

;chez chez-lib.sc play-piano.sc
;mychez play-piano.sc
;(load "c:/path/to/chez-lib/lib.sc") ;

;(play-hz-s mus-1)

#|
ty
234  78 0-=
qwerguiop[]
sdf  jk ;'\
zxcv m,./
|#

(setq
  *key2doremi*
  `(
    [#\6     Mu  ]
    [#\b     Mu  ]
    [#\return  #\return ] ;
    [#\newline #\newline] ;
    [#\2     Fa2 ]
    [#\3     So2 ]
    [#\4     La2 ]
    [#\7     Do2.]
    [#\8     Re2.]
    [#\0     Fa2.]
    [#\-     So2.]
    [#\=     La2.]
    [#\q     Fa  ]
    [#\w     So  ]
    [#\e     La  ]
    [#\r     Si  ]
    [#\g     Do. ]
    [#\h     Do. ]
    [#\u     Re. ]
    [#\i     Mi. ]
    [#\o     Fa. ]
    [#\p     So. ]
    [#\[     La. ]
    [#\]     Si. ]
    [#\s     .Fa2]
    [#\d     .So2]
    [#\f     .La2]
    [#\j     Do2 ]
    [#\k     Re2 ]
    [#\;     Fa2 ]
    [#\'     So2 ]
    [#\\     La2 ]
    [#\z     .Fa ]
    [#\x     .So ]
    [#\c     .La ]
    [#\v     .Si ]
    [#\space Do  ]
    [#\m     Re  ]
    [#\,     Mi  ]
    [#\.     Fa  ]
    [#\/     So  ]
) )

; h8877hh7h34b 477hh44h4we

(def [play-piano]
  (let ~ ([c (read-char)] [scale 0]) ;init
    (if [eq c #\`] nil ;exit
      (let ([note (key->val key2doremi c eq id T nil)]) ;.
        (case c
          [#\t (-= scale 1)] ;++
          [#\y (+= scale 1)]
          (else
            (if (nilp note) nil
              (bgn
                (case c
                  [#\return  nil] ;
                  [#\newline nil] ;
                  (else                  
                    (play-hz (* [ev note] [pow 2 scale])) ;
                ) )                      
                (echo note)
        ) ) ) )
        (~ [read-char] scale) ;each
) ) ) )

;(play-piano)
