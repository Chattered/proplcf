(require 'magit)
(require 'haskell)
(require 'haskell-interactive-mode)
(require 'haskell-indentation)
(add-hook 'haskell-mode-hook 'interactive-haskell-mode)
(add-hook 'haskell-mode-hook 'haskell-indentation-mode)
(add-hook 'haskell-mode-hook 'whitespace-mode)
