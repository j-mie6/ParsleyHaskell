{-# LANGUAGE TemplateHaskell, UnboxedTuples #-}
module Parsley.Register.Test where
import Test.Tasty
import Test.Tasty.HUnit

import Prelude hiding ()
import Parsley (runParser, code)

tests :: TestTree
tests = testGroup "Register" [ newRegisterTests
                             , getTests
                             , putTests
                             , getsTests
                             , modifyTests
                             , moveTests
                             , swapTests
                             , localTests
                             , bindTests
                             , rollbackTests
                             , forTests
                             ]

newRegisterTests :: TestTree
newRegisterTests = testGroup "newRegister should" [] -- newRegister_

getTests :: TestTree
getTests = testGroup "get should" []

putTests :: TestTree
putTests = testGroup "put should" [] -- put_

getsTests :: TestTree
getsTests = testGroup "gets should" [] -- gets_

modifyTests :: TestTree
modifyTests = testGroup "modify should" [] -- modify_

moveTests :: TestTree
moveTests = testGroup "move should" []

swapTests :: TestTree
swapTests = testGroup "swap should" []

localTests :: TestTree
localTests = testGroup "local should" []

bindTests :: TestTree
bindTests = testGroup "bind should" []

rollbackTests :: TestTree
rollbackTests = testGroup "rollback should" []

forTests :: TestTree
forTests = testGroup "for should" []