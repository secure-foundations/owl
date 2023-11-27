" OWL highlight
if version < 600
    syntax clear
elseif exists("b:current_syntax")
    finish
endif

syn keyword owlConditional case if guard then else pack unpack
syn keyword owlCommand input output requires ensures
syn keyword owlDecl name func def locality enum struct table module type corr counter
syn keyword owlKeyword let in return get_counter inc_counter aenc adec aenc_with_nonce adec_with_nonce sign vrfy mac mac_vrfy adv ghost 

syn keyword owlTypeName Data Name Option Ghost
syn region owlCommentLine                                                  start="//"                      end="$" 
syn region owlCommentBlock             matchgroup=owlCommentBlock         start="/\*\%(!\|\*[*/]\@!\)\@!" end="\*/" 

hi def link owlDecl Include
hi def link owlTypeName Type
hi def link owlCommentLine Comment
hi def link owlCommentBlock Comment
hi def link owlCommand Typedef
hi def link owlKeyword Keyword

let b:current_syntax = 'owl'


