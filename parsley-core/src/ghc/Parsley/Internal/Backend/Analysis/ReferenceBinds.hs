{-|
Module      : Parsley.Internal.Backend.Analysis.ReferenceBinds
Description : Translation of Combinator AST into Machine
License     : BSD-3-Clause
Maintainer  : TBD
Stability   : experimental

This module exports an optimisation pass `bindReferences` that will attach `MetaInstr`s for each return continuation, join points, handler
telling which references might live through that code element. This allows for the full tenderisation of registers
by making every reference access `Soft`. 

The determination of free references at each point is much alike to the algorithm performed in `Parsley.Internal.Frontend.Analysis.Dependencies`.

-}
module Parsley.Internal.Backend.Analysis.ReferenceBinds () where
import Parsley.Internal.Common (Fix4, HFresh, MonadFresh (..))
import Parsley.Internal.Backend.Machine (Instr (..), SomeΣVar, Handler (..))
import Parsley.Internal.Common.Indexed (Nat, Fix4 (..), Const4 (..), cata4)
import Data.Kind (Type)

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Parsley.Internal.Common.Indexed (Const4)
import Parsley.Internal.Common.Fresh (runFresh)

bindReferences :: Fix4 (Instr o) xs n r a -> Fix4 (Instr o) xs n r a
bindReferences instrs = instrs
    where
        -- 1. tag the instructions
        (taggedInstrs, maxTag) = tagInstructions instrs

        -- 2. Perform liveness analysis to get map of Instruction ID -> (liveIn, liveOut)
        liveSets = liveness maxTag taggedInstrs

        -- 3. Use `liveSets` to tag each join point, handler, and return continuation with references that might live through it
        instrs' = markThreadables liveSets taggedInstrs


-- We need to tag each instruction with a unique ID so we can perform liveness analysis
data Tag4 t f (k :: [Type] -> Nat -> Type -> Type ->  Type) (xs :: [Type]) (n :: Nat) r a = Tag4 {tag :: t, tagged :: f k xs n r a}
type InstrID = Int
type TaggedInstr a = Tag4 InstrID (Instr a)
newtype Tagger o xs n r a = Tagger {doTagger :: HFresh InstrID (Fix4 (TaggedInstr o) xs n r a)}

tagInstructions :: Fix4 (Instr o) xs n r a -> (Fix4 (TaggedInstr o) xs n r a, Int)
tagInstructions instrs = runFresh (doTagger $ cata4 alg instrs) initID
    where
        initID = 0 :: InstrID

        wrap p = newVar >>= (\t -> return (In4 (Tag4 t p)))

        alg :: Instr o (Tagger o) xs n r a -> Tagger o xs n r a
        alg Ret                 = Tagger $ wrap Ret
        alg (Call μ k)          = Tagger $ do doTagger k >>= (wrap . Call μ)
        alg (Push x k)          = Tagger $ do doTagger k >>= (wrap . Push x)
        alg (Pop k)             = Tagger $ do doTagger k >>= (wrap . Pop)
        alg (Lift2 f k)         = Tagger $ do doTagger k >>= (wrap . Lift2 f)
        alg (Sat f k)           = Tagger $ do doTagger k >>= (wrap . Sat f)
        alg Empt                = Tagger $ wrap Empt
        alg (Commit k)          = Tagger $ do doTagger k >>= (wrap . Commit)
        alg (Catch p h)         = Tagger $ do
                                    p' <- doTagger p 
                                    h' <- case h of  
                                        (Same a ka b kb) -> do 
                                                                ka' <- doTagger ka 
                                                                kb' <- doTagger kb
                                                                return $ Same a ka' b kb'
                                        (Always x k) -> do 
                                                                k' <- doTagger k
                                                                return $ Always x k' 
                                    wrap (Catch p' h')
        alg (Tell k)            = Tagger $ do doTagger k >>= (wrap . Tell)
        alg (Seek k)            = Tagger $ do doTagger k >>= (wrap . Seek)
        alg (Case p q)          = Tagger $ do 
                                    p' <- doTagger p 
                                    q' <- doTagger q 
                                    wrap (Case p' q')
        alg (Choices fs ks def) = Tagger $ do 
                                    ks' <- traverse doTagger ks
                                    def' <- doTagger def
                                    wrap (Choices fs ks' def')
        alg (Iter μ l h)        = Tagger $ do 
                                    l' <- doTagger l
                                    h' <- case h of  
                                        (Same a ka b kb) -> do 
                                                                ka' <- doTagger ka 
                                                                kb' <- doTagger kb
                                                                return $ Same a ka' b kb'
                                        (Always x k) -> do 
                                                                k' <- doTagger k
                                                                return $ Always x k'
                                    wrap (Iter μ l' h') 
        alg (Join φ)            = Tagger $ wrap (Join φ)
        alg (MkJoin φ p k)      = Tagger $ do 
                                    p' <- doTagger p 
                                    k' <- doTagger k 
                                    wrap (MkJoin φ p' k')
        alg (Swap k)            = Tagger $ do doTagger k >>= (wrap . Swap)
        alg (Dup k)             = Tagger $ do doTagger k >>= (wrap . Dup)
        alg (Make σ a k)        = Tagger $ do doTagger k >>= (wrap . Make σ a)
        alg (Get σ a k)         = Tagger $ do doTagger k >>= (wrap . Get σ a)
        alg (Put σ a k)         = Tagger $ do doTagger k >>= (wrap . Put σ a)
        alg (SelectPos p k)     = Tagger $ do doTagger k >>= (wrap . SelectPos p)
        alg (LogEnter l k)      = Tagger $ do doTagger k >>= (wrap . LogEnter l)
        alg (LogExit l k)       = Tagger $ do doTagger k >>= (wrap . LogExit l)
        alg (MetaInstr m k)     = Tagger $ do doTagger k >>= (wrap . MetaInstr m)

type LivenessSets = Map InstrID (Set SomeΣVar, Set SomeΣVar)

liveness :: InstrID -> Fix4 (TaggedInstr o) xs n r a -> LivenessSets
liveness = undefined

markThreadables :: LivenessSets -> Fix4 (TaggedInstr o) xs n r a -> Fix4 (Instr o) xs n r a
markThreadables = undefined
