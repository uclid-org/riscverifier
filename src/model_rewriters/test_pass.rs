use asts::veriv_ast;
use std::cell::RefCell;

pub struct TestPass;
impl veriv_ast::ASTRewriter<()> for TestPass {
    fn rewrite_expr_literal(expr: veriv_ast::Expr, _context: &RefCell<()>) -> veriv_ast::Expr {
        use veriv_ast::*;
        match expr {
            Expr::Literal(Literal::Bv { val, width:_ }, _) => {
                let rw_lit = Literal::Int { val };
                let rw_typ = Type::Int;
                Expr::Literal(rw_lit, rw_typ)
            },
            _ => panic!("Expected Expr::Literal."),
        }
    }
}
