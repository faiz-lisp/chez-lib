
; Play piano with Windows API Beep

;chez chez-lib.sc play-piano.sc
;mychez play-piano.sc
;(load "c:/path/to/chez-lib/lib.sc") ;

#|
= Update notes
  - if note? note else hz
|#

;(play-hzs mus-1)

(alias *key2doremi* *key2doremi-1*)

#|
ty
234  78 0-=
qwerguiop[]
sdf  jk ;'\
zxcv m,./
|#

(setq
  *key2doremi-1*
  `(
    [#\6      Mu  ]
    [#\b      Mu  ]
    [#\return #\return] ;
   [#\newline #\newline] ;
    [#\2      Fa2 ]
    [#\3      So2 ]
    [#\4      La2 ]
    [#\7      Do2.]
    [#\8      Re2.]
    [#\0      Fa2.]
    [#\-      So2.]
    [#\=      La2.]
    [#\q      Fa  ]
    [#\w      So  ]
    [#\e      La  ]
    [#\r      Si  ]
    [#\g      Do. ]
    [#\h      Do. ]
    [#\u      Re. ]
    [#\i      Mi. ]
    [#\o      Fa. ]
    [#\p      So. ]
    [#\[      La. ]
    [#\]      Si. ]
    [#\s     .Fa2 ]
    [#\d     .So2 ]
    [#\f     .La2 ] ;
    [#\j      Do2 ]
    [#\k      Re2 ]
    [#\;      Fa2 ]
    [#\'      So2 ]
    [#\\      La2 ]
    [#\z     .Fa  ]
    [#\x     .So  ]
    [#\c     .La  ]
    [#\v     .Si  ]
    [#\space  Do  ]
    [#\m      Re  ]
    [#\,      Mi  ]
    [#\.      Fa  ]
    [#\/      So  ]
) )

; h8877hh7h34b 477hh44h4we

#|
~
qwer uiop[]
4567 234567.
asdf jkl;'\
xzcv nm,./
Shift
8
1234567  -- scale-x
!@ -= () -- scale
#$ 90 _+ -- dura-ms
|#

;sometime will exit, maybe caused by beep ?
(def (play-piano)
  (let ([getter read-char] [scale (- 4 4)] [note? T]) ;read/put-char
    (let ~ ([c (getter)]) ;- init offs
      (if (eq c #\`) nil ;exit
        (let ([note (key->val *key2doremi* c eq id T nil)]) ;.
          (case c
            [#\~ (setq note? (! note?))]
            [#\t (-= scale 1)] ;++ ;
            [#\y (+= scale 1)]
            (else
              (if~
                (nilp note)
                  nil
                (sym? note) ;char?
                  (let ([hz (* [ev note] (pow 2 scale))])
                    (play-hz hz)
                    (echo [if note? note (str hz " ")]) )
                (echo note)
          ) ) )
          (~ [getter])
) ) ) ) )

;(play-piano)
