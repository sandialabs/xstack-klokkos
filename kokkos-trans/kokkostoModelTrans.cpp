
#include "clang/AST/ASTContext.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendAction.h"
#include "clang/Rewrite/Core/Rewriter.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Tooling.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Regex.h"

using namespace clang;
using namespace clang::tooling;
static llvm::cl::OptionCategory KokkosTransCategory("KlokkosTrans options");

AST_MATCHER_FUNCTION(ast_matchers::internal::Matcher<FunctionDecl>,
                     kokkosParallelXFunctionDecl) {
  using namespace clang::ast_matchers;
  return functionDecl(matchesName("::Kokkos::parallel_.*"));
}

AST_MATCHER(CallExpr, isKokkosParallelCall) {
  using namespace clang::ast_matchers;
  if (auto const *FD = Node.getDirectCallee()) {
    std::string Name = FD->getQualifiedNameAsString();
    StringRef SR(Name);
    if (SR.startswith("::Kokkos::parallel_") ||
        SR.startswith("Kokkos::parallel_")) {
      return true;
    }
   //    if (SR.startswith("::KokkosModelLB::region") ||
    //    SR.startswith("KokkosModelLB::region")) {
     //  return true;
     //  }
  }

  return false;
}

// helper
namespace __internal__ {
    void convertHeaderFileName(llvm::SmallString<256> &OutputFileName) {
        if (llvm::sys::path::extension(OutputFileName).equals(".hpp")) {
            llvm::sys::path::replace_extension(OutputFileName, "trans.hpp");
        } else if (llvm::sys::path::extension(OutputFileName).equals(".h")) {
            llvm::sys::path::replace_extension(OutputFileName, "trans.h");
        }
    }

    bool insideForStmt(const Stmt *s, const ForStmt **loop, ASTContext *ctx) {
        while(true) {
            const auto& parents = ctx->getParents(*s);
            llvm::errs() << "find parent size=" << parents.size() << "\n";
            s = parents[0].get<Stmt>();
            if (!s)
                return false;
#if 0
            s->dump();
#endif
            if (isa<ForStmt>(s)) {
                *loop = dyn_cast<ForStmt>(s);
                return true;
            }
        }
        return false;
    }

    std::array<std::string, 2> generateCheckpointCalls(std::vector<std::string> &vars) {
#if 0
        std::string mes = "\nstd::vector<Kokkos::ViewBase*> vect" + LN + "(";
        for (unsigned int i = 0; i < vars.size(); i++) {
            mes += vars[i];
            if (i < vars.size() - 1) mes += ", ";
        }
        mes +=  ");\n";
        mes += "checkpoint(vect" + LN + ");";
#else
        std::string pre = "KokkosModelRuntimeLB::beginRegion();\n";
        
        for(auto var : vars){
            pre += "KokkosModelRuntimeLB::register_view(" + var + ");\n";
        }

        pre += "KokkosModelRuntimeLB::run([&]{\n";

        std::string post = "});\n";
        
        post += "KokkosModel::endRegion();\n";

#endif
        std::array<std::string, 2> toReturn = {pre, post};
        return toReturn;
    }
// This is where KokkosViewRead and KokkosViewAssign need to be translated . 
    bool searchInStmt(const Stmt *s, const ValueDecl* var, bool isLambda) {
        const CXXOperatorCallExpr *op = dyn_cast<CXXOperatorCallExpr>(s);
        if (op) {
            for (auto const &p : op->children()) {
                const Stmt* r;
                const ImplicitCastExpr *ice = dyn_cast<ImplicitCastExpr>(p);
                if (ice) {
                    r = ice->getSubExpr();
                } else {
                    r = p;
                }
                if (!isLambda) {
                    // Functor
                    const MemberExpr *q = dyn_cast<MemberExpr>(r);
                    if (q) {
                        const ValueDecl* d = q->getMemberDecl();
                        if (d == var) {
                            return true;
                        }
                    }
                } else {
                    // Lambda
                    const DeclRefExpr *q = dyn_cast<DeclRefExpr>(r);
                    if (q) {
                        const ValueDecl* d = q->getDecl();
                        if (d == var) {
                            return true;
                        }
                    }
                }
            }
        }
        for (auto const &p : s->children()) {
            bool ret = searchInStmt(p, var, isLambda);
            if (ret) return true;
        }
        return false;
    }

    bool foundInFunctionCall_helper(const ASTContext *Context, const Stmt *s, const ValueDecl* var, bool isLambda) {
        if (!s || !var) return false;
        if (const CallExpr *CE = dyn_cast<CallExpr>(s)) {
            if (const FunctionDecl *fd = CE->getDirectCallee()) {
                std::string funcName = fd->getQualifiedNameAsString();
                if (funcName.find("Kokkos::atomic") != std::string::npos) {
#if 0
                    llvm::errs() << funcName << " var: " << var->getName() << "\n";
                    var->dump();
#endif
                    auto arg = CE->getArg(0);
                    // FIXME (generalize)
                    const ImplicitCastExpr *ice = dyn_cast<ImplicitCastExpr>(arg);
                    if (ice) {
                        const ImplicitCastExpr *ice2 = dyn_cast<ImplicitCastExpr>(ice->getSubExpr());
                        if (ice2) {
                        if (const DeclRefExpr *q = dyn_cast<DeclRefExpr>(ice2->getSubExpr())) {
                            const VarDecl *decl = dyn_cast<VarDecl>(q->getDecl());
                            if (decl) {
                                bool ret = searchInStmt(decl->getInit(), var, isLambda);
                                if (ret) return true;
                            }
                        }
                        }
                    }
                } else {
                    llvm::errs() << "foundInFunctionCall inspecting: " << funcName << "\n";
                    unsigned i = 0;
                    for (auto const p : fd->parameters()) {
                        llvm::errs() << "here-1\n";
                        auto concreteT = p->getOriginalType().getDesugaredType(*Context);
                        auto tname = concreteT.getAsString();
                        auto arg = CE->getArg(i);
                        llvm::errs() << "here-1" << tname << "\n";
                        if (tname.find("Kokkos::View") != std::string::npos) {
                            llvm::errs() << "this argument is Kokkos::View\n";
                            if (tname.find("const") == std::string::npos) {
                                llvm::errs() << "and is not const either\n";
                                const CXXBindTemporaryExpr *CBTE = dyn_cast<CXXBindTemporaryExpr>(arg);
                                if (CBTE) {
                                    llvm::errs() << "here-4\n";
                                    CBTE->dump();
                                    const CXXConstructExpr *CCE  = dyn_cast<CXXConstructExpr>(CBTE->getSubExpr());
                                    for (auto q : CCE->arguments()) {
                                        if (!isLambda) {
                                            const MemberExpr *r = dyn_cast<MemberExpr>(q);
                                            if (r) {
                                                if (r->getMemberDecl() == var) {
                                                    return true;
                                                }
                                            }
                                        } else {
                                            // Lambda
                                            const DeclRefExpr *r = dyn_cast<DeclRefExpr>(q);
                                            if (r) {
                                                const ValueDecl* d = r->getDecl();
                                                if (d == var) {
                                                    return true;
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                        i++;
                    }
                }
            }
        }
        llvm::errs() << "exit\n";
        return false;
    }

    bool foundInFunctionCall(const ASTContext *Context, const Stmt *s, const ValueDecl* var, bool isLambda) {
        if (!s) return false;
        if(foundInFunctionCall_helper(Context, s, var, isLambda)) {
            return true;
        }

        for (auto const &p : s->children()) {
            bool ret = foundInFunctionCall(Context, p, var, isLambda);
            if (ret) return true;
        }
        return false;
    }

    bool foundInSubView_helper(const Stmt *s, const ValueDecl* var, bool isLambda) {
        if (!s) return false;
        if (const CallExpr *CE = dyn_cast<CallExpr>(s)) {
            if (const FunctionDecl* fd = CE->getDirectCallee()) {
                if (fd->getNameInfo().getName().getAsString().compare("subview") == 0) {
                    //llvm::errs() << fd->getNameInfo().getName().getAsString() << "\n";
                    if (!isLambda) {
                        if (const MemberExpr* me = dyn_cast<MemberExpr>(CE->getArg(0))) {
                            if (me->getMemberDecl() == var) {
                                return true;
                            }
                        }
                    } else {
                        if (const DeclRefExpr* drf = dyn_cast<DeclRefExpr>(CE->getArg(0))) {
                            if (drf->getDecl() == var) {
                                return true;
                            }
                        }
                    }

#if 0
                    if (const CXXConstructExpr* cxxce = dyn_cast<CXXConstructExpr>(CE->getArg(0))) {
                    }
#endif
                }
            }
        }
        return false;
    }

    bool foundInSubView(const Stmt *s, const ValueDecl* var, bool isLambda) {
        if (!s) return false;
        if(foundInSubView_helper(s, var, isLambda)) {
            return true;
        }

        for (auto const &p : s->children()) {
            bool ret = foundInSubView(p, var, isLambda);
            if (ret) return true;
        }
        return false;
    }

    bool foundInLHS_helper(const Stmt *s, const ValueDecl *var, bool isLambda) {
        if (const BinaryOperator *BO = dyn_cast<BinaryOperator>(s)) {
            if (BO->isAssignmentOp()) {
                Expr *lhs = BO->getLHS();
                CXXOperatorCallExpr *op = dyn_cast<CXXOperatorCallExpr>(lhs);
                if (op) {
                    for (auto const &p : op->children()) {
                        const Stmt* r;
                        const ImplicitCastExpr *ice = dyn_cast<ImplicitCastExpr>(p);
                        if (ice) {
                            r = ice->getSubExpr();
                        } else {
                            r = p;
                        }
                        if (!isLambda) {
                            // Functor 
                            const MemberExpr *q = dyn_cast<MemberExpr>(r);
                            if (q) {
                                const ValueDecl* d = q->getMemberDecl();
                                if (d == var) {
                                    return true;
                                }
                            }
                        } else {
                            // Lambda
                            const DeclRefExpr *q = dyn_cast<DeclRefExpr>(r);
                            if (q) {
                                const ValueDecl* d = q->getDecl();
                                if (d == var) {
                                    return true;
                                }
                            }
                        }
                    }
                }
            }
        }
        return false;
    }

    bool foundInLHS(const Stmt *s, const ValueDecl *var, bool isLambda) {
        if (!s) return false;
        if (foundInLHS_helper(s, var, isLambda)) {
            return true;
        }

        for (auto const &p : s->children()) {
            bool ret = foundInLHS(p, var, isLambda);
            if (ret) return true;
        }
        return false;
    }

    bool toBeCheckpointed(const ASTContext *Context, const Stmt *body, const ValueDecl* var, bool isLambda) {
        clang::DiagnosticsEngine &DE = Context->getDiagnostics();
        const unsigned ID = DE.getCustomDiagID(clang::DiagnosticsEngine::Remark, "%0 will be transformed to Kokkos Model (Found in LHS)");
        const unsigned ID_SUBVIEW = DE.getCustomDiagID(clang::DiagnosticsEngine::Remark, "View::subview detected, working with the full view (%0) .");
        const unsigned ID_FUNC = DE.getCustomDiagID(clang::DiagnosticsEngine::Remark, "%0 will be transformed to Kokkos Model (Found in function call)");
        const unsigned ID_RO = DE.getCustomDiagID(clang::DiagnosticsEngine::Remark, "%0 will not be transformed because it's read-only.");
        const unsigned ID_TALIAS = DE.getCustomDiagID(clang::DiagnosticsEngine::Remark, "Desugar %0 <- %1");

        auto tname = var->getType().getAsString();
        // Check if the type of the current captured var is Kokkos::View
        if (tname.find("Kokkos::View") != std::string::npos) {
            // Check if it's readonly or not 
            if (__internal__::foundInLHS(body, var, isLambda)) {
                DE.Report(body->getBeginLoc(), ID).AddString(var->getName());
                return true;
            }
            //  subview(View, ...);
            if (__internal__::foundInSubView(body, var, isLambda)) {
                DE.Report(body->getBeginLoc(), ID_SUBVIEW).AddString(var->getName());
                return true;
            }
            //  func(View, ...); 
            if (__internal__::foundInFunctionCall(Context, body, var, isLambda)) {
                DE.Report(body->getBeginLoc(), ID_FUNC).AddString(var->getName());
                return true;
            }
            DE.Report(body->getBeginLoc(), ID_RO).AddString(var->getName());
        } else {
            // or typedef'ed
            // Get concrete type: return QualType
            auto concreteT = var->getType().getDesugaredType(*Context);
            auto tname2 = concreteT.getAsString();
            if (tname2.find("Kokkos::View") != std::string::npos) {
                DE.Report(body->getBeginLoc(), ID_TALIAS).AddString(var->getType().getAsString()); 
                DE.Report(body->getBeginLoc(), ID_TALIAS).AddString(tname2);
                if (__internal__::foundInLHS(body, var, isLambda)) {
                    DE.Report(body->getBeginLoc(), ID).AddString(var->getName());
                    return true;
                }
                //  subview(View, ...);
                if (__internal__::foundInSubView(body, var, isLambda)) {
                    DE.Report(body->getBeginLoc(), ID_SUBVIEW).AddString(var->getName());
                    return true;
                }
                //  func(View, ...); 
                if (__internal__::foundInFunctionCall(Context, body, var, isLambda)) {
                    DE.Report(body->getBeginLoc(), ID_FUNC).AddString(var->getName());
                    return true; 
                }
                DE.Report(body->getBeginLoc(), ID_RO).AddString(var->getName());
            }
        }
        return false;
    }
}

using namespace clang::ast_matchers;

class ForHandler : public MatchFinder::MatchCallback {
public:
    ForHandler(Rewriter &R) : TheRewriter(R) {};
    virtual void run(const MatchFinder::MatchResult &Result) {
        static std::vector<const ForStmt*> processed;
        auto const *loop = Result.Nodes.getNodeAs<ForStmt>("for");
        if (std::find(processed.begin(), processed.end(), loop) != processed.end()) {
            return;
        }
        processed.push_back(loop);
        SourceManager &SM = TheRewriter.getSourceMgr();
        if (SM.getFileID(loop->getBeginLoc()) == SM.getMainFileID()) {
          // Starting Klokkos parallel region (transformed from Kokkos) for Klee here 
            if (TheRewriter.InsertText(loop->getBeginLoc(), "ParallelForRangePolicyInit();\n ", true, true)) {}
            loop->getInit()->dump();
            const ValueDecl * var;
            if (const DeclRefExpr *declExpr = dyn_cast<DeclRefExpr>(loop->getInit())) {
                var = declExpr->getDecl();
            }
            if (!var) {
                if (const DeclStmt *declStmt = dyn_cast<DeclStmt>(loop->getInit())) {
                    var = dyn_cast<ValueDecl>(declStmt->getSingleDecl());
                }
            }
            if (var) {
                const Stmt *body = loop->getBody();
                //auto opt = clang::Lexer::findNextToken(body->getBeginLoc(), TheRewriter.getSourceMgr(), TheRewriter.getLangOpts());
                auto opt = clang::Lexer::findNextToken(loop->getRParenLoc(), TheRewriter.getSourceMgr(), TheRewriter.getLangOpts());
                if (opt.hasValue()) {
                    SourceLocation begin = opt.getValue().getLocation();
                    auto opt2 = clang::Lexer::findNextToken(begin, TheRewriter.getSourceMgr(), TheRewriter.getLangOpts());
                    if (opt2.hasValue()) {
                        SourceLocation begin2 = opt2.getValue().getLocation(); 
                                // Starting Klokkos parallel for region (transformed from Kokkos)
                         
                       auto ls = llvm::Twine("ParallelForRangePolicyBegin(" + var->getName() + ", " + lb->getName() + ", " + ub->getName() + ", DefaultExecSpace);\n").str();
                        if (TheRewriter.InsertText(begin2, ls, false, true)) {
                        }
                    }
                } else {
                    assert(false && "");
                }
                SourceLocation end = body->getEndLoc();
              
                        // Ending Klokkos parallel region (transformed from Kokkos) for Klee here 

               auto le = llvm::Twine("ParallelForRangePolicyEnd(" + var->getName() + ");\n").str();
                 auto lb = var; 
                 auto ub = var; 
        
                // auto le = llvm::Twine("ParallelForRangePolicyEnd(" + var->getName() + ", " + lb->getName() + ", " + ub->getName() + ", DefaultExecSpace);\n").str();

                if (TheRewriter.InsertText(end, le, true, true)) {
                }
            } else {
                assert(false && "");
            }
            auto loop_exit = clang::Lexer::findNextToken(loop->getEndLoc(), TheRewriter.getSourceMgr(), TheRewriter.getLangOpts());
            if (loop_exit.hasValue()) {
                        // Ending Klokkos parallel loop region (transformed from Kokkos) for Klee here 

                if (TheRewriter.InsertText(loop_exit.getValue().getLocation(), "ParallelForRangePolicyFini();\n", true, true)) {}
            }
        }
    }
private:
    Rewriter &TheRewriter;
};

class KokkosParallelForFunctorHandler : public MatchFinder::MatchCallback {
public:

    KokkosParallelForFunctorHandler(Rewriter &R, std::vector<FileID> &H) : TheRewriter(R), TranslatedFiles(H) {};
    virtual void run(const MatchFinder::MatchResult &Result) {
        ASTContext *Context = Result.Context;
        auto const *pfor = Result.Nodes.getNodeAs<CallExpr>("y");
        auto const *functor = Result.Nodes.getNodeAs<DeclRefExpr>("Functor");
        clang::DiagnosticsEngine &DE = Context->getDiagnostics();
        const unsigned ID_pfor = DE.getCustomDiagID(clang::DiagnosticsEngine::Remark, "parallel_for being analyzed");
        const unsigned ID_start = DE.getCustomDiagID(clang::DiagnosticsEngine::Remark, "being analyzed (start)");
        const unsigned ID_end = DE.getCustomDiagID(clang::DiagnosticsEngine::Remark, "being analyzed (end)");

        // check
        if (!pfor || !functor) {
            return;
        }

        DE.Report(pfor->getBeginLoc(), ID_pfor);
        const ValueDecl* valued = functor->getDecl();
        const CXXRecordDecl* classdecl = valued->getType().getTypePtr()->getAsCXXRecordDecl();

        if (!classdecl) {
            DE.Report(pfor->getBeginLoc(), DE.getCustomDiagID(clang::DiagnosticsEngine::Remark, "classdecl is NULL"));
            return;
        }

        std::vector<std::string> vars;
        unsigned int count = 0;
        const CXXMethodDecl *opdecl;
        for (auto m = classdecl->method_begin(); m != classdecl->method_end(); m++) {
            CXXMethodDecl *md = dyn_cast<CXXMethodDecl>(*m);
            if (md) {
                if (md->getOverloadedOperator() == OO_Call) {
                    opdecl = md;
                    count++;
                }
            }
        }
        assert(count == 1);
        DE.Report(opdecl->getBeginLoc(), ID_start);
        DE.Report(opdecl->getEndLoc(), ID_end);
        for (auto p = classdecl->decls_begin(); p != classdecl->decls_end(); p++) {
            FieldDecl *fd = dyn_cast<FieldDecl>(*p);
            if (fd) {
                if (__internal__::toBeCheckpointed(Context, opdecl->getBody(), fd, false)) {
                    vars.push_back(fd->getName().str());
                }
            }
        }

        // Replacement 1 : operator() {} -> operator() {} void checkpoint() { checkpoint(); ... };
        auto endOfOperatorCallToken = clang::Lexer::findNextToken(opdecl->getEndLoc(), TheRewriter.getSourceMgr(), TheRewriter.getLangOpts());
        SourceManager &SM = TheRewriter.getSourceMgr();
        if (endOfOperatorCallToken.hasValue()) {
            SourceLocation endOfOperatorCall = endOfOperatorCallToken.getValue().getLocation();
            static std::vector<SourceLocation> processed;
            FileID FID = SM.getFileID(endOfOperatorCall);
            std::array<std::string, 2> mess = __internal__::generateCheckpointCalls(vars);
            std::string checkpoint_function = "/*Auto-generated from parallel_for at: " + pfor->getBeginLoc().printToString(SM) + "*/\n";
            if (std::find(processed.begin(), processed.end(), endOfOperatorCall) == processed.end()) {
                checkpoint_function += "template<typename F>\n";
                checkpoint_function += "void point(F fun){\n";
                checkpoint_function += mess[0];
                checkpoint_function += "fun();";
                checkpoint_function += mess[1];
                checkpoint_function += "}";
            }
            processed.push_back(endOfOperatorCall);
            
            if (TheRewriter.InsertText(endOfOperatorCall, checkpoint_function, false, true)) {
                llvm::errs() << opdecl->getBeginLoc().printToString(SM) << " is not rewritable\n";
            } else { 
                // Functor definition is not in the main file but in a header file
                if (FID != SM.getMainFileID()) {
                    StringRef name = SM.getFileEntryForID(FID)->getName();
                    llvm::errs() << SM.getFileEntryForID(FID)->getName() << " is not MainFile\n";
                    // the location of #include ""
                    //                          ^
                    SourceLocation includeLoc = SM.getIncludeLoc(FID);
                    // check if it's already translated
                    if (std::find(TranslatedFiles.begin(), TranslatedFiles.end(), FID) == TranslatedFiles.end()) {

                        // the corresponding token
                        Token t;
                        clang::Lexer::getRawToken(includeLoc, t, SM, TheRewriter.getLangOpts(), true);
                        // include ""
                        if (t.isLiteral()) {
                            // t.getLiteral() = "a.hpp" <- includes ""
                            StringRef data(t.getLiteralData(), t.getLength());
                            SmallString<256> OutputFileName(data.trim("\""));
                            __internal__::convertHeaderFileName(OutputFileName);
                            auto Output = llvm::Twine("\"" + OutputFileName + "\"").str();
                            if (!TheRewriter.ReplaceText(includeLoc, Output)) {
                                // Bookkeeping the replaced file
                                TranslatedFiles.push_back(FID);
                            }
                            // include <>
                        } else if (t.getKind() == tok::less) {
                            Token current = t;

                            SourceLocation endOfInclude;
                            llvm::Optional<Token> next = Lexer::findNextToken(current.getLocation(), SM, TheRewriter.getLangOpts());
                            while (next.hasValue()) {
                                auto token = next.getValue();
                                if (token.getKind() == tok::greater) {
                                    endOfInclude = token.getLocation();
                                    break;
                                }
                                if (token.getKind() == tok::eof) {
                                    llvm::errs() << "reached eof\n";
                                }
                                current = token;
                                next = Lexer::findNextToken(current.getLocation(), SM, TheRewriter.getLangOpts());
                            }
                            StringRef data = Lexer::getSourceText(CharSourceRange::getTokenRange(includeLoc, endOfInclude), SM, TheRewriter.getLangOpts());
                            SmallString<256> OutputFileName(data.trim("<").trim(">"));
                            __internal__::convertHeaderFileName(OutputFileName);
                            auto Output = llvm::Twine("<" + OutputFileName + ">").str();
                            if (!TheRewriter.ReplaceText(CharSourceRange::getTokenRange(includeLoc, endOfInclude), Output)) {
                                // Bookkeeping the replaced file
                                TranslatedFiles.push_back(FID);
                            }
                        } else {
                            llvm::errs() << "The include file is specified not in "" or <>: " << includeLoc.printToString(SM) << "\n";
                            llvm::errs() << "Token name: " << t.getName() << "\n";
                        }
                    }
                }
            }
        } else {
            llvm_unreachable("could not find where to put Klokkos Model LB API");
        }
        // Replacement 2 : parallel_for(functor); -> parallel_for(functor); functor.profilelb();
        SourceLocation endOfParallelForCall = clang::Lexer::findLocationAfterToken(pfor->getEndLoc(), tok::semi, TheRewriter.getSourceMgr(), TheRewriter.getLangOpts(), false);
        static std::vector<SourceLocation> processed;
        if (std::find(processed.begin(), processed.end(), endOfParallelForCall) == processed.end()) {
            std::string mes1 = valued->getName().str() + ".profilelb([&]{";
            std::string mes2 = "});";
            if (TheRewriter.InsertText(pfor->getBeginLoc(), mes1, true, true) || 
                TheRewriter.InsertText(endOfParallelForCall, mes2, true, true)) {
                llvm::errs() << pfor->getBeginLoc().printToString(SM) << " is not rewritable OR\n";
                llvm::errs() << endOfParallelForCall.printToString(SM) << " is not rewritable\n";
            }
            processed.push_back(endOfParallelForCall);
        }
    }
private:
    Rewriter &TheRewriter;
    std::vector<FileID> &TranslatedFiles;
};

class KokkosParallelForHandler : public MatchFinder::MatchCallback {
public:
    KokkosParallelForHandler(Rewriter &R) : TheRewriter(R) {};

    virtual void run(const MatchFinder::MatchResult &Result) {
        ASTContext *Context = Result.Context;
        auto const *pfor = Result.Nodes.getNodeAs<CallExpr>("x");
        const ForStmt *loop;
        if (__internal__::insideForStmt(pfor, &loop, Context)) {
#if 0
            if (TheRewriter.InsertText(loop->getBeginLoc(), "KokkosModelLB::loop_enter();\n", true, true)) {}
            if (const DeclStmt *declStmt = dyn_cast<DeclStmt>(loop->getInit())) {
                if (const ValueDecl *var = dyn_cast<ValueDecl>(declStmt->getSingleDecl())) {
                    const Stmt *body = loop->getBody();
                    auto opt = clang::Lexer::findNextToken(body->getBeginLoc(), TheRewriter.getSourceMgr(), TheRewriter.getLangOpts());
                    if (opt.hasValue()) {
                        SourceLocation begin = opt.getValue().getLocation();
                        auto ls = llvm::Twine("KokkosParallelFor_Start(" + var->getName() + ");\n").str();
                        if (TheRewriter.InsertText(begin, ls, true, true)) {
                        }
                    } else {
                        assert(false && "");
                    }
                    SourceLocation end = body->getEndLoc();
                    auto le = llvm::Twine("KokkosParallelFor_End(" + var->getName() + ");\n").str();
                    if (TheRewriter.InsertText(end, le, true, true)) {
                    }
                } else {
                    assert(false && "");
                }
            }
            auto loop_exit = clang::Lexer::findNextToken(loop->getEndLoc(), TheRewriter.getSourceMgr(), TheRewriter.getLangOpts());
            if (loop_exit.hasValue()) {
                if (TheRewriter.InsertText(loop_exit.getValue().getLocation(), "KokkosParallelFor_fini();\n", true, true)) {}
            }
#endif
        }
        if (pfor) {
            auto const *Lambda = Result.Nodes.getNodeAs<CXXRecordDecl>("Lambda");
            if (Lambda->isLambda()) {
                std::vector<std::string> vars;
                auto const *mDecl = Lambda->getLambdaCallOperator();
                if (mDecl->hasBody()) {
                    for (auto const &Capture : Lambda->captures()) {
                        auto const var = Capture.getCapturedVar();
                        if (__internal__::toBeCheckpointed(Context, mDecl->getBody(), var, true)) { // note: need to develop different internal function call here
                            vars.push_back(var->getName().str());
                        }
                    }
                    if (!vars.empty()) {
                        SourceLocation endOfCall = clang::Lexer::findLocationAfterToken(pfor->getEndLoc(), tok::semi, TheRewriter.getSourceMgr(), TheRewriter.getLangOpts(), false);
                        FullSourceLoc FullLocation = Context->getFullLoc(endOfCall); 
                        std::string LN = std::to_string(FullLocation.getSpellingLineNumber());
                        
                        std::array<std::string, 2> mess = __internal__::generateCheckpointCalls(vars); // note: need to develop different internal function call here

                        if (TheRewriter.InsertText(pfor->getBeginLoc(), mess[0], true, true) || 
                            TheRewriter.InsertText(endOfCall, mess[1], true, true)) {
                        }
                    }
                }
            }
        }
    }
private:
    Rewriter &TheRewriter;
};

class KokkosTransConsumer : public clang::ASTConsumer {
public:
    explicit KokkosTransConsumer(Rewriter &R, std::vector<FileID> &H)
        : HandlerForParallelFor(R), HandlerForParallelForFunctor(R, H), HandlerForForLoop(R) {//, HandlerForParallelForFunctorDecl(R) {
        auto isAllowedPolicy = expr(hasType(
                                        cxxRecordDecl(matchesName("::Impl::ThreadVectorRangeBoundariesStruct.*|"
                                                                  "::Impl::TeamThreadRangeBoundariesStruct.*"))));
        //
        Matcher.addMatcher(forStmt().bind("for"),
                           &HandlerForForLoop);

        // parallel_for(, ... lambda)
        auto Lambda = expr(hasType(cxxRecordDecl(isLambda()).bind("Lambda")));
        Matcher.addMatcher(callExpr(isKokkosParallelCall(), hasAnyArgument(Lambda),
                                     unless(hasAnyArgument(isAllowedPolicy)))
                            .bind("x"),
                            &HandlerForParallelFor);

        // parallel_for(, ... functor)
        //auto Functor = expr(declRefExpr().bind("Functor"));
        auto Functor = expr(declRefExpr(to(varDecl(hasType(cxxRecordDecl())))).bind("Functor"));
        Matcher.addMatcher(callExpr(isKokkosParallelCall(), hasAnyArgument(Functor),
                                    unless(hasAnyArgument(isAllowedPolicy)))
                           .bind("y"),
                           &HandlerForParallelForFunctor);
    }

    virtual void HandleTranslationUnit(clang::ASTContext &Context) {
        // Run the matchers when we have the whole TU parsed.
        Matcher.matchAST(Context);
    }
private:
    KokkosParallelForHandler HandlerForParallelFor;
    KokkosParallelForFunctorHandler HandlerForParallelForFunctor;
    ForHandler HandlerForForLoop;
    MatchFinder Matcher;
};

class KokkoTransAction : public clang::ASTFrontendAction {
public:
    void EndSourceFileAction() override {
        SourceManager &SM = TheRewriter.getSourceMgr();
        llvm::errs() << "** EndSourceFileAction for: "
                     << SM.getFileEntryForID(SM.getMainFileID())->getName() << "\n";

        //
        if (!TranslatedFiles.empty()) {
            // remove duplicates
            sort( TranslatedFiles.begin(), TranslatedFiles.end() );
            TranslatedFiles.erase( unique( TranslatedFiles.begin(), TranslatedFiles.end() ), TranslatedFiles.end() );
            for (FileID &fid: TranslatedFiles) {
                const FileEntry *entry = SM.getFileEntryForID(fid);
                //
                llvm::SmallString<256> OutputDirectory(entry->getName());
                llvm::SmallString<256> OutputFileName(llvm::sys::path::filename(entry->getName()));
                llvm::sys::path::remove_filename(OutputDirectory);

                __internal__::convertHeaderFileName(OutputFileName);

                if (char *dir = getenv("KOKKOS_CLANG_HEADER_OUTPUT_DIR")) {
                    llvm::errs() << "** KOKKOS_CLANG_HEADER_OUTPUT_DIR is set to: " << dir << "\n";
                    OutputDirectory.assign(dir);
                }

                auto Output = llvm::Twine(OutputDirectory.str() + "/" + OutputFileName.str()).str();

                llvm::errs() << "** Translating from " <<  entry->getName() << " to " << Output << "\n";
                std::error_code EC;
                llvm::raw_fd_ostream fout(Output, EC, llvm::sys::fs::CD_CreateAlways);
                TheRewriter.getEditBuffer(fid).write(fout);
            }
        }

        // Translate the mainfile
        // Note: the output is stdout
        static bool WroteMain = false; //Only write to stdout for one file, covering edge case.
        if(!WroteMain){
            TheRewriter.getEditBuffer(SM.getMainFileID()).write(llvm::outs());
            WroteMain = true;
        } else {
            llvm::errs() << "** Warning, multiple compile definitions found for primary file. Using the first found.\n";
        }
    }

    virtual std::unique_ptr<clang::ASTConsumer> CreateASTConsumer(
        clang::CompilerInstance &Compiler, llvm::StringRef InFile) {
        llvm::errs() << "** Creating AST consumer for: " << InFile << "\n"; 
        TheRewriter.setSourceMgr(Compiler.getSourceManager(), Compiler.getLangOpts());
        return std::unique_ptr<clang::ASTConsumer>(
            new KokkosTransConsumer(TheRewriter, TranslatedFiles));
    }
private:
    Rewriter TheRewriter;
    std::vector<FileID> TranslatedFiles;
    bool WroteMain = false;
};

int main(int argc, const char **argv) {
    llvm::Expected<CommonOptionsParser> option = CommonOptionsParser::create(argc, argv, KokkosTransCategory, llvm::cl::OneOrMore);
    if (option) {
        ClangTool Tool(option->getCompilations(),
                       option->getSourcePathList());

        return Tool.run(newFrontendActionFactory<KokkoTransAction>().get());
    } else {
         llvm::errs() << "arg error\n";
    }
}
