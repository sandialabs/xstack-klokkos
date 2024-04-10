// This translates a clang AST into the Sage AST so that the clang frontend can be used where needed but allows for modifications of the AST 

bool ClangToSageTranslator::VisitFunctionDecl(clang::FunctionDecl * function_decl, SgNode ** node) { 
   SgName name(function_decl->getNameAsString());
   SgType * ret_type = SageBuilder::buildTypeFromQualifiedType(function_decl->getReturnType()); 
   SgFunctionParameterList * param_list = SageBuilder::buildFunctionParameterList_nfi();
   applySourceRange(param_list, function_decl->getSourceRange());
   for (unsigned i = 0; i < function_decl->getNumParams(); i++) {
    SgNode * tmp_init_name = Traverse(function_decl->getParamDecl(i));
    SgInitializedName * init_name = isSgInitializedName(tmp_init_name);
    param_list->append_arg(init_name);
  }
 SgFunctionDeclaration * sg_function_decl;
 sg_function_decl = SageBuilder::buildNondefiningFunctionDeclaration(name,
 ret_type, param_list, NULL);
 SgInitializedNamePtrList & init_names = param_list->get_args();
 // ... // rest of conversion
   *node = sg_function_decl;
    return VisitDeclaratorDecl(function_decl, node) && res;
}
