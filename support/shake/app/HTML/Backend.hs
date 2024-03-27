-- Copyright (c) 2005-2021 remains with the Agda authors. See /support/shake/LICENSE.agda

-- | Backend for generating highlighted, hyperlinked HTML from Agda sources.
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DerivingStrategies #-}
module HTML.Backend
  ( htmlBackend
  , compileOneModule
  , moduleName
  , defaultHtmlOptions
  ) where

import HTML.Base

import Prelude hiding ((!!), concatMap)
import Control.Monad.Identity
import Control.Monad.Except

import qualified Data.HashMap.Strict as Hm
import qualified Data.Map.Strict as Map
import qualified Data.HashSet as HashSet
import qualified Data.Text as Text
import Data.HashMap.Strict (HashMap)
import Data.List.NonEmpty (NonEmpty((:|)))
import Data.Map.Strict (Map)
import Data.Foldable
import Data.HashSet (HashSet)
import Data.Aeson
import Data.IORef
import Data.Text (Text)
import Data.List

import Agda.Compiler.Backend
import Agda.Compiler.Common

import qualified Agda.Syntax.Concrete.Generic as Con
import qualified Agda.Syntax.Internal.Generic as I
import qualified Agda.Syntax.Abstract.Views as A
import qualified Agda.Syntax.Internal as I
import qualified Agda.Syntax.Abstract as A
import qualified Agda.Syntax.Concrete as Con
import qualified Agda.Syntax.Scope.Base as Scope

import Agda.Syntax.Translation.InternalToAbstract ( Reify(reify) )
import Agda.Syntax.Translation.AbstractToConcrete (abstractToConcrete_)
import Agda.Syntax.TopLevelModuleName
import Agda.Syntax.Abstract.Views
import Agda.Syntax.Common.Pretty
import Agda.Syntax.Abstract hiding (Type)
import Agda.Syntax.Position
import Agda.Syntax.Internal (Type, domName)
import Agda.Syntax.Common
import Agda.Syntax.Info

import Agda.TypeChecking.Reduce (instantiateFull, reduceDefCopyTCM, normalise)

import Agda.Utils.FileName

import System.FilePath hiding (normalise)
import Debug.Trace
import qualified Agda.Utils.Maybe.Strict as S
import Agda.Syntax.Scope.Monad (modifyCurrentScope)
import Agda.Syntax.Abstract.Pretty (prettyA)
import Agda.TypeChecking.Records (isRecord)
import Data.Set (Set)
import qualified Data.Set as Set
import Agda.TypeChecking.Level (reallyUnLevelView)

data HtmlCompileEnv = HtmlCompileEnv
  { htmlCompileEnvOpts     :: HtmlOptions
  , htmlCompileTypes       :: IORef (HashMap Text Identifier)
    -- ^ Hashmap from anchor→identifier for finding types while emitting
    -- HTML, and for search after
  }

data HtmlModuleEnv = HtmlModuleEnv
  { htmlModEnvCompileEnv :: HtmlCompileEnv
  , htmlModEnvName       :: TopLevelModuleName
  }

newtype HtmlModule = HtmlModule { getHtmlModule :: HashMap Text Identifier }

htmlBackend :: FilePath -> HtmlOptions -> Backend
htmlBackend = (Backend .) . htmlBackend'

htmlBackend'
  :: FilePath
  -> HtmlOptions
  -> Backend'
      (FilePath, HtmlOptions)
      HtmlCompileEnv
      HtmlModuleEnv
      HtmlModule
      (Maybe (Text, Identifier))
htmlBackend' basepn opts = Backend'
  { backendName = "HTML"
  , backendVersion = Nothing
  , options = (basepn, opts)
  , commandLineFlags = []
  , isEnabled = const True
  , preCompile = preCompileHtml
  , preModule = preModuleHtml
  , compileDef = compileDefHtml
  , postModule = postModuleHtml
  , postCompile = postCompileHtml
  , scopeCheckingSuffices = False
  , mayEraseType = const $ return False
  }

runLogHtmlWithMonadDebug :: MonadDebug m => LogHtmlT m a -> m a
runLogHtmlWithMonadDebug = runLogHtmlWith $ reportS "html" 1

preCompileHtml
  :: (MonadIO m, MonadDebug m)
  => (FilePath, HtmlOptions)
  -> m HtmlCompileEnv
preCompileHtml (_pn, opts) = do
  types <- liftIO (newIORef mempty)
  runLogHtmlWithMonadDebug $ pure $ HtmlCompileEnv opts types

preModuleHtml
  :: (MonadIO m, ReadTCState m)
  => HtmlCompileEnv
  -> IsMain
  -> TopLevelModuleName
  -> Maybe FilePath
  -> m (Recompile HtmlModuleEnv HtmlModule)
preModuleHtml cenv _isMain topl _ifacePath
  | htmlOptGenTypes (htmlCompileEnvOpts cenv) = do
    liftIO . putStrLn $ "Entering module " <> render (pretty topl)
    pure $ Recompile (HtmlModuleEnv cenv topl)
-- When types are being skipped we can safely only re-render modules
-- whose interface file have changed:
preModuleHtml cenv _ modName mifile =
  do
    ft <- iFileType <$> curIF
    let
      ext = highlightedFileExt (htmlOptHighlight (htmlCompileEnvOpts cenv)) ft
      path = htmlOptDir (htmlCompileEnvOpts cenv) </> modToFile modName ext

    liftIO $ do
      uptd <- uptodate path
      if uptd
        then do
          putStrLn $ "HTML for module " <> render (pretty modName) <> " is up-to-date"
          pure $ Skip (HtmlModule mempty)
        else pure $ Recompile (HtmlModuleEnv cenv modName)

  where
    uptodate of_ = case mifile of
      Nothing -> pure False
      Just ifile -> isNewerThan of_ ifile

compileDefHtml
  :: HtmlCompileEnv
  -> HtmlModuleEnv
  -> IsMain
  -> Definition
  -> TCM (Maybe (Text, Identifier))
compileDefHtml env _ _ _
  | not (htmlOptGenTypes (htmlCompileEnvOpts env)) = pure Nothing
compileDefHtml env _menv _isMain def = withCurrentModule (qnameModule (defName def)) $
  case definitionAnchor env def of
    Just mn -> do
      ty <- typeToText def
      let
        ident = Identifier
          { idAnchor = mn
          , idIdent  = Text.pack (render (pretty (qnameName (defName def))))
          , idType   = ty
          }
      pure (Just (mn, ident))
    Nothing -> do
      pure Nothing

postModuleHtml
  :: (MonadIO m, MonadDebug m, ReadTCState m)
  => HtmlCompileEnv
  -> HtmlModuleEnv
  -> IsMain
  -> TopLevelModuleName
  -> [Maybe (Text, Identifier)]
  -> m HtmlModule
postModuleHtml env menv _isMain _modName _defs = do
  let
    ins Nothing = id
    ins (Just (a, b)) = Hm.insert a b

  types <- liftIO $ atomicModifyIORef' (htmlCompileTypes env) $
    \mp -> let mp' = foldr ins mp _defs in (mp', mp')

  let
    generatePage =
        defaultPageGen types
      . htmlCompileEnvOpts
      . htmlModEnvCompileEnv
      $ menv
  htmlSrc <- srcFileOfInterface (htmlModEnvName menv) <$> curIF
  runLogHtmlWithMonadDebug $ generatePage htmlSrc
  pure $ HtmlModule $ foldr ins mempty _defs

postCompileHtml
  :: MonadIO m
  => HtmlCompileEnv
  -> IsMain
  -> Map TopLevelModuleName HtmlModule
  -> m ()
postCompileHtml cenv _isMain _modulesByName = liftIO $ do
  case htmlOptDumpIdents (htmlCompileEnvOpts cenv) of
    Just fp -> encodeFile fp (Map.elems _modulesByName >>= Hm.elems . getHtmlModule)
    Nothing -> pure ()

-- | Compile a single module, given an existing set of types.
compileOneModule
  :: FilePath -> HtmlOptions
  -> HashMap Text Identifier -- ^ Existing map of identifiers to their types.
  -> Interface -- ^ The interface to compile.
  -> TCM ()
compileOneModule _pn opts types iface = do
  types <- liftIO (newIORef types)
  let cEnv = HtmlCompileEnv opts types
      mEnv = HtmlModuleEnv cEnv (iTopLevelModuleName iface)

  setInterface iface

  defs <- map snd . sortDefs <$> curDefs
  res  <- mapM (compDef cEnv mEnv <=< instantiateFull) defs
  _ <- postModuleHtml cEnv mEnv NotMain (iTopLevelModuleName iface) res
  pure ()

  where
    compDef env menv def = setCurrentRange (defName def) $
      compileDefHtml env menv NotMain def

prettifyTerm :: I.Type -> TCM I.Type
prettifyTerm =
  let
    fixProj :: I.Elim -> I.Elim
    fixProj (I.Proj _ x) = I.Proj ProjPostfix x
    fixProj e = e

    saturated :: QName -> [I.Elim] -> Bool
    saturated q x
      | Just as <- I.allApplyElims x
      = Con.numHoles q == length (filter visible as)
      | otherwise = False

    unspine :: I.Term -> TCM I.Term
    unspine tm = pure $! case I.unSpine tm of
      uns@(I.Def prj args) | saturated prj args -> uns
      _ -> tm

    step = \case
      I.Pi d x -> pure $ I.Pi d{I.domName = Nothing} x

      I.Def q x
        | isExtendedLambdaName q -> pure (I.Def q x)
        | isAbsurdLambdaName q   -> pure (I.Def q x)
        | saturated q x          -> pure (I.Def q x)

      I.Def q x -> reduceDefCopyTCM q x >>= \case
        YesReduction _ t -> step t
        _ | Just _ <- I.allApplyElims x -> do
          fv <- inTopContext (length <$> lookupSection (qnameModule q))
          pure $ I.Def q (drop fv x)
        _ | otherwise -> unspine (I.Def q x)

      I.Con o q x -> unspine $ I.Con o q (map fixProj x)
      I.Var i x   -> unspine $ I.Var i (map fixProj x)
      x           -> pure x
  in I.traverseTermM step

killQual :: Con.Expr -> Con.Expr
killQual = Con.mapExpr (wrap . forget) where
  work :: Con.QName -> Con.QName
  work (Con.Qual _ x) = work x
  work x = x

  forget :: Con.Expr -> Con.Expr
  forget (Con.KnownOpApp r w qual names args) = Con.OpApp w qual names args
  forget (Con.KnownIdent r nm) = Con.Ident nm
  forget x = x

  wrap :: Con.Expr -> Con.Expr
  wrap (Con.Ident v)                 = Con.Ident (work v)
  wrap (Con.KnownIdent v w)          = Con.KnownIdent v (work w)
  wrap (Con.OpApp v qual names args) = Con.OpApp v (work qual) names args
  wrap x = x

getClass :: QName -> TCM (Set QName)
getClass q = isRecord q >>= \case
  Just Record{ recFields = f } -> pure $! Set.fromList (map I.unDom f)
  _ -> pure mempty

usedInstances :: I.TermLike a => a -> TCM (Set QName)
usedInstances =
  let
    getClass q = isRecord q >>= \case
      Just Record{ recFields = f } -> pure $! Set.fromList (map I.unDom f)
      _ -> pure mempty
  in
    I.foldTerm \case
      I.Def q _ -> do
        def <- getConstInfo q
        case Agda.Compiler.Backend.defInstance def of
          Just c  -> Set.insert q <$> getClass (instanceClass c)
          Nothing -> pure mempty
      _ -> pure mempty

typeToText :: Definition -> TCM Text
typeToText d = do
  ui <- usedInstances (I.unEl (defType d))
  ty <- locallyReduceDefs (OnlyReduceDefs ui) $ normalise (defType d)
  tm <- prettifyTerm ty
  expr <- runNoCopy (reify tm)
  fmap (Text.pack . render . pretty . killQual) .
    abstractToConcrete_ . removeImpls $ expr

removeImpls :: A.Expr -> A.Expr
removeImpls (A.Pi _ (x :| xs) e) =
  makePi (map (A.mapExpr removeImpls) $ filter ((/= Hidden) . getHiding) (x:xs)) (removeImpls e)
removeImpls (A.Fun span arg ret) =
  A.Fun span (removeImpls <$> arg) (removeImpls ret)
removeImpls e = e

makePi :: [A.TypedBinding] -> A.Expr -> A.Expr
makePi [] = id
makePi (b:bs) = A.Pi exprNoRange (b :| bs)

newtype NoCopy a = NoCopy { runNoCopy :: TCM a }
  deriving newtype (Functor, Applicative, Monad, MonadFail)
  deriving newtype
    ( HasBuiltins, MonadDebug, MonadReduce, HasOptions, MonadTCEnv
    , ReadTCState, MonadAddContext, MonadInteractionPoints
    , MonadFresh NameId
    )

noCopyOp :: Definition -> Definition
noCopyOp def | defCopy def, Con.numHoles (defName def) >= 1 = traceShow (pretty (defName def)) $ def{defCopy = False}
noCopyOp def = def

instance HasConstInfo NoCopy where
  getConstInfo = NoCopy . fmap noCopyOp . getConstInfo
  getConstInfo' = NoCopy . fmap (fmap noCopyOp) . getConstInfo'
  getRewriteRulesFor = NoCopy . getRewriteRulesFor

instance PureTCM NoCopy

definitionAnchor :: HtmlCompileEnv -> Definition -> Maybe Text
definitionAnchor _ def | defCopy def = Nothing
definitionAnchor _ def = f =<< go where
  go :: Maybe FilePath
  go = do
    let name = defName def
    case rangeModule (nameBindingSite (qnameName name)) of
      Just f -> Just (modToFile f "html")
      Nothing -> Nothing
  f modn =
    case rStart (nameBindingSite (qnameName (defName def))) of
      Just pn -> pure $ Text.pack (modn <> "#" <> show (posPos pn))
      Nothing -> Nothing

-- | Determine the name of a module from a file like @1Lab/HIT/Torus@.
moduleName :: FilePath -> String
moduleName = intercalate "." . splitDirectories
