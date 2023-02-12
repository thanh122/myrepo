//===- StringObfuscation.cpp - Obfuscates the usage of static string constants
//---------------===//

#include "light_vm.h"

#include <fcntl.h>
#include <unistd.h>

#include <cassert>
#include <fstream>
#include <map>
#include <set>
#include <string>
#include <unordered_map>
#include <vector>

#include "llvm/ADT/Statistic.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalValue.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/NoFolder.h"
#include "llvm/IR/Type.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils/ValueMapper.h"
#include "utils/CryptoUtils.h"
#include "utils/Utils.h"

using namespace std;
using namespace llvm;

#define DEBUG_TYPE "MyVM"

namespace llvm {

std::string MyVMObfuscation::readAnnotate(Function *f) {
    std::string annotation = "";
    // Get annotation variable
    GlobalVariable *glob =
        f->getParent()->getGlobalVariable("llvm.global.annotations");
    if (!glob) {
        return annotation;
    }
    // Get the array
    ConstantArray *ca = dyn_cast<ConstantArray>(glob->getInitializer());
    if (!ca) {
        return annotation;
    }
    for (unsigned i = 0; i < ca->getNumOperands(); ++i) {
        // Get the struct
        ConstantStruct *structAn = dyn_cast<ConstantStruct>(ca->getOperand(i));
        if (!structAn) {
            continue;
        }
        ConstantExpr *expr = dyn_cast<ConstantExpr>(structAn->getOperand(0));
        if (!expr) {
            continue;
        }
        // If it's a bitcast we can check if the annotation
        // is concerning the current function
        if (expr->getOpcode() == Instruction::BitCast &&
            expr->getOperand(0) == f) {
            ConstantExpr *note = cast<ConstantExpr>(structAn->getOperand(1));
            // If it's a GetElementPtr, that means we found
            // the variable containing the annotations
            if (note->getOpcode() == Instruction::GetElementPtr) {
                if (GlobalVariable *annoteStr =
                        dyn_cast<GlobalVariable>(note->getOperand(0))) {
                    if (ConstantDataSequential *data =
                            dyn_cast<ConstantDataSequential>(
                                annoteStr->getInitializer())) {
                        if (data->isString()) {
                            annotation += data->getAsString().str() + " ";
                        }
                    }
                }
            }
        }
    }
    return annotation;
}

bool MyVMObfuscation::isPHINodeBranchInst(Instruction &insn) {
    if (isa<BranchInst>(insn)) {
        BranchInst *bran_inst = cast<BranchInst>(&insn);
        for (auto *succ : bran_inst->successors()) {
            for (auto ins_it = succ->begin(); ins_it != succ->end(); ++ins_it) {
                if (isa<PHINode>(*ins_it)) {
                    return true;
                }
            }
        }
    }
    if (isa<InvokeInst>(insn)) {
        InvokeInst *invoke_ins = cast<InvokeInst>(&insn);
        for (size_t i = 0; i < 2; i++) {
            auto *succ = invoke_ins->getSuccessor(i);
            for (auto ins_it = succ->begin(); ins_it != succ->end(); ++ins_it) {
                if (isa<PHINode>(*ins_it)) {
                    return true;
                }
            }
        }
    }
    return false;
}

int MyVMObfuscation::getRandInt32() {
    return llvm::cryptoutils->get_uint32_t();
}

short MyVMObfuscation::getRandInt16() {
    return llvm::cryptoutils->get_uint16_t();
}

/* createAlteredBasicBlock
 *
 * This function return a basic block similar to a given one.
 * It's inserted just after the given basic block.
 * The instructions are similar but junk instructions are added between
 * the cloned one. The cloned instructions' phi nodes, metadatas, uses and
 * debug locations are adjusted to fit in the cloned basic block and
 * behave nicely.
 */
BasicBlock *MyVMObfuscation::createAlteredBasicBlock(BasicBlock *basicBlock,
                                                     const Twine &Name) {
    // Useful to remap the informations concerning instructions.
    ValueToValueMapTy VMap;
    BasicBlock *alteredBB =
        BasicBlock::Create(basicBlock->getContext(), "junkbb",
                           basicBlock->getParent(), basicBlock);
    alteredBB->moveAfter(basicBlock);

    for (auto &insn : *basicBlock) {
        Instruction *clone_insn = insn.clone();
        alteredBB->getInstList().push_back(clone_insn);
        VMap[&insn] = clone_insn;
    }

    // Remap operands.
    BasicBlock::iterator ji = basicBlock->begin();
    for (BasicBlock::iterator i = alteredBB->begin(), e = alteredBB->end();
         i != e; ++i) {
        // Loop over the operands of the instruction
        for (User::op_iterator opi = i->op_begin(), ope = i->op_end();
             opi != ope; ++opi) {
            // get the value for the operand
            Value *v = MapValue(*opi, VMap, RF_None, 0);
            if (v != 0) {
                *opi = v;
            }
        }
        // Remap phi nodes' incoming blocks.
        if (PHINode *pn = dyn_cast<PHINode>(i)) {
            for (unsigned j = 0, e = pn->getNumIncomingValues(); j != e; ++j) {
                Value *v = MapValue(pn->getIncomingBlock(j), VMap, RF_None, 0);
                if (v != 0) {
                    pn->setIncomingBlock(j, cast<BasicBlock>(v));
                }
            }
        }
        // Remap attached metadata.
        SmallVector<std::pair<unsigned, MDNode *>, 4> MDs;
        i->getAllMetadata(MDs);
        // important for compiling with DWARF, using option -g.
        i->setDebugLoc(ji->getDebugLoc());
        ji++;
    }  // The instructions' informations are now all correct

    // add random instruction in the middle of the bloc. This part can be
    // improve
    for (BasicBlock::iterator i = alteredBB->begin(), e = alteredBB->end();
         i != e; ++i) {
        // in the case we find binary operator, we modify slightly this part
        // by randomly insert some instructions
        if (i->isBinaryOp()) {  // binary instructions
            unsigned opcode = i->getOpcode();
            BinaryOperator *op, *op1 = NULL;
            Twine *var = new Twine("_");
            // treat differently float or int
            // Binary int
            if (opcode == Instruction::Add || opcode == Instruction::Sub ||
                opcode == Instruction::Mul || opcode == Instruction::UDiv ||
                opcode == Instruction::SDiv || opcode == Instruction::URem ||
                opcode == Instruction::SRem || opcode == Instruction::Shl ||
                opcode == Instruction::LShr || opcode == Instruction::AShr ||
                opcode == Instruction::And || opcode == Instruction::Or ||
                opcode == Instruction::Xor) {
                for (int random = getRandInt32() % 10; random < 10; ++random) {
                    switch (getRandInt32() % 4) {  // to improve
                        case 0:                    // do nothing
                            break;
                        case 1:
                            op = BinaryOperator::CreateNeg(i->getOperand(0),
                                                           *var, &*i);
                            op1 = BinaryOperator::Create(Instruction::Add, op,
                                                         i->getOperand(1),
                                                         "gen", &*i);
                            break;
                        case 2:
                            op1 = BinaryOperator::Create(
                                Instruction::Sub, i->getOperand(0),
                                i->getOperand(1), *var, &*i);
                            op = BinaryOperator::Create(Instruction::Mul, op1,
                                                        i->getOperand(1), "gen",
                                                        &*i);
                            break;
                        case 3:
                            op = BinaryOperator::Create(
                                Instruction::Shl, i->getOperand(0),
                                i->getOperand(1), *var, &*i);
                            break;
                    }
                }
            }
            // Binary float
            if (opcode == Instruction::FAdd || opcode == Instruction::FSub ||
                opcode == Instruction::FMul || opcode == Instruction::FDiv ||
                opcode == Instruction::FRem) {
                for (int random = getRandInt32() % 10; random < 10; ++random) {
                    switch (getRandInt32() % 3) {  // can be improved
                        case 0:                    // do nothing
                            break;
                        case 1:
                            op = BinaryOperator::CreateFDiv(
                                i->getOperand(0), i->getOperand(1), *var, &*i);
                            op1 = BinaryOperator::Create(Instruction::FAdd, op,
                                                         i->getOperand(1),
                                                         "gen", &*i);
                            break;
                        case 2:
                            op = BinaryOperator::Create(
                                Instruction::FSub, i->getOperand(0),
                                i->getOperand(1), *var, &*i);
                            op1 = BinaryOperator::Create(Instruction::FMul, op,
                                                         i->getOperand(1),
                                                         "gen", &*i);
                            break;
                    }
                }
            }
            if (opcode == Instruction::ICmp) {  // Condition (with int)
                ICmpInst *currentI = (ICmpInst *)(&i);
                switch (getRandInt32() % 3) {  // must be improved
                    case 0:                    // do nothing
                        break;
                    case 1:
                        currentI->swapOperands();
                        break;
                    case 2:  // randomly change the predicate
                        switch (getRandInt32() % 10) {
                            case 0:
                                currentI->setPredicate(ICmpInst::ICMP_EQ);
                                break;  // equal
                            case 1:
                                currentI->setPredicate(ICmpInst::ICMP_NE);
                                break;  // not equal
                            case 2:
                                currentI->setPredicate(ICmpInst::ICMP_UGT);
                                break;  // unsigned greater than
                            case 3:
                                currentI->setPredicate(ICmpInst::ICMP_UGE);
                                break;  // unsigned greater or equal
                            case 4:
                                currentI->setPredicate(ICmpInst::ICMP_ULT);
                                break;  // unsigned less than
                            case 5:
                                currentI->setPredicate(ICmpInst::ICMP_ULE);
                                break;  // unsigned less or equal
                            case 6:
                                currentI->setPredicate(ICmpInst::ICMP_SGT);
                                break;  // signed greater than
                            case 7:
                                currentI->setPredicate(ICmpInst::ICMP_SGE);
                                break;  // signed greater or equal
                            case 8:
                                currentI->setPredicate(ICmpInst::ICMP_SLT);
                                break;  // signed less than
                            case 9:
                                currentI->setPredicate(ICmpInst::ICMP_SLE);
                                break;  // signed less or equal
                        }
                        break;
                }
            }
            if (opcode == Instruction::FCmp) {  // Conditions (with float)
                FCmpInst *currentI = (FCmpInst *)(&i);
                switch (getRandInt32() % 3) {  // must be improved
                    case 0:                    // do nothing
                        break;
                    case 1:
                        currentI->swapOperands();
                        break;
                    case 2:  // randomly change the predicate
                        switch (getRandInt32() % 10) {
                            case 0:
                                currentI->setPredicate(FCmpInst::FCMP_OEQ);
                                break;  // ordered and equal
                            case 1:
                                currentI->setPredicate(FCmpInst::FCMP_ONE);
                                break;  // ordered and operands are unequal
                            case 2:
                                currentI->setPredicate(FCmpInst::FCMP_UGT);
                                break;  // unordered or greater than
                            case 3:
                                currentI->setPredicate(FCmpInst::FCMP_UGE);
                                break;  // unordered, or greater than, or
                                        // equal
                            case 4:
                                currentI->setPredicate(FCmpInst::FCMP_ULT);
                                break;  // unordered or less than
                            case 5:
                                currentI->setPredicate(FCmpInst::FCMP_ULE);
                                break;  // unordered, or less than, or equal
                            case 6:
                                currentI->setPredicate(FCmpInst::FCMP_OGT);
                                break;  // ordered and greater than
                            case 7:
                                currentI->setPredicate(FCmpInst::FCMP_OGE);
                                break;  // ordered and greater than or equal
                            case 8:
                                currentI->setPredicate(FCmpInst::FCMP_OLT);
                                break;  // ordered and less than
                            case 9:
                                currentI->setPredicate(FCmpInst::FCMP_OLE);
                                break;  // ordered or less than, or equal
                        }
                        break;
                }
            }
        }
    }
    return alteredBB;
}

// The premise that the quadratic equation ax^2 + bx + c = 0 has a solution
// is that b^2 - 4ac > 0 Generate a, b, c that do not meet this condition
void MyVMObfuscation::get_a_b_c(int &a, int &b, int &c) {
    b = getRandInt16();
    long bb = b * b;
    long ac4;
    do {
        a = getRandInt16();
        c = getRandInt16();
        ac4 = 4 * a * c;
    } while (bb >= ac4);
}

// build opaque predicate
// dst was originally the successor of src
bool MyVMObfuscation::insert_opaque_predicate(BasicBlock *src,
                                              BasicBlock *dst) {
    if (src == nullptr || dst == nullptr || dst->empty()) return false;

    auto *terminator = src->getTerminator();
    if (isa<BranchInst>(terminator)) {
        BranchInst *inst = cast<BranchInst>(terminator);
        if (inst->isConditional()) {
            return false;
        }
    }

    // If dst is phinode, it will not be inserted
    auto first = dst->begin();
    if (isa<PHINode>(&(*first))) {
        return false;
    }

    LLVMContext &context = src->getContext();
    IRBuilder<> builder(context);

    // clear end br
    terminator->eraseFromParent();

    // Create junk bb
    BasicBlock *junk_bb = this->createAlteredBasicBlock(dst);

    // construct opaque predicate
    builder.SetInsertPoint(src, src->end());
    int a, b, c;
    get_a_b_c(a, b, c);
    Value *con_a = ConstantInt::get(Type::getInt32Ty(context), a);
    Value *con_b = ConstantInt::get(Type::getInt32Ty(context), b);
    Value *con_c = ConstantInt::get(Type::getInt32Ty(context), c);
    Value *con_0 = ConstantInt::get(Type::getInt32Ty(context), 0);
    // a*x^2+b*x+c==0
    Value *x = builder.CreateAlloca(Type::getInt32Ty(context), nullptr, "x");
    builder.CreateLifetimeStart(x);
    Value *x_load = builder.CreateLoad(Type::getInt32Ty(context), x, "x_load");
    Value *xx = builder.CreateMul(x_load, x_load);
    Value *axx = builder.CreateMul(xx, con_a);
    Value *bx = builder.CreateMul(x_load, con_b);
    Value *add1 = builder.CreateAdd(axx, bx);
    Value *add2 = builder.CreateAdd(add1, con_c);

    Value *cmp = builder.CreateCmp(CmpInst::Predicate::ICMP_NE, add2, con_0);
    builder.CreateLifetimeEnd(x);
    builder.CreateCondBr(cmp, dst, junk_bb);
    return true;
}

bool has_phi_node(BasicBlock *bb) {
    for (Instruction &I : *bb) {
        if (isa<PHINode>(I)) {
            return true;
        }
    }
    return false;
}

bool MyVMObfuscation::runOnFunction(Function &F) {
    errs() << F.getName()
           << " =================== start =======================\n";
    // Check if declaration
    if (F.isDeclaration()) {
        return false;
    }

    // Check external linkage
    if (F.hasAvailableExternallyLinkage() != 0) {
        return false;
    }

    // Insert a bb before the entrybb of the function to store temporary
    // variables
    BasicBlock *fn_new_entry_bb =
        BasicBlock::Create(F.getContext(), "fn_entry", &F, &F.getEntryBlock());

    // dbg purpose
    size_t count_VMInterpreterHandler = 0;

    std::vector<BasicBlock *> to_earse_bbs;
    int count = 0;

    // remove all lifetime because it does not work with switchinst in our VM
    vector<Instruction *> remove_life_time;
    for (auto &orgBB : F) {
        for (auto &ins : orgBB) {
            if (isa<CallInst>(&ins)) {
                CallInst *c_inst = cast<CallInst>(&ins);
                auto f = c_inst->getCalledFunction();
                string f_name(f->getName());
                if (match(f_name, "llvm.lifetime.end*") ||
                    match(f_name, "llvm.lifetime.start*")) {
                    remove_life_time.push_back(&ins);
                    continue;
                }
            }
        }
    }
    for (auto i : remove_life_time) {
        i->removeFromParent();
        i->deleteValue();
    }

    LLVMContext &context = F.getContext();
    IRBuilder<> builder(context);
    vector<BasicBlock *> all_dup_handler;
    unordered_map<string, ReplaceItem> replace_map;
    set<string> all_dup_load;
    set<string> all_dup_store;

    for (BasicBlock &originBB : F) {
        if (count == 0 && originBB.getName() == "fn_entry") {
            continue;
        }

        std::vector<BasicBlock *> handlerbb_list;

        std::string name = "OriginBB" + std::to_string(count++);
        originBB.setName(name);

        if (!originBB.empty()) {
            // PHI NODE must be in the first conditional instruction of the
            // block
            Instruction &insn = *(originBB.begin());
            if (isa<PHINode>(insn)) {
                errs() << "Processing bb has PHINODE " << name << "\n";
                all_dup_handler.push_back(&originBB);
                continue;
            }

            if (originBB.size() <= 2) {
                errs() << "BB size less than 2\n";
                all_dup_handler.push_back(&originBB);
                continue;
            }
        }

        // skip exception handler block
        if (originBB.empty() || originBB.isEHPad()) {
            continue;
        };

        // VMInterpreterBody
        BasicBlock *VMInterpreterbody_bb =
            BasicBlock::Create(context, "VMInterpreterBody", &F, &originBB);
        // VMInterpreter
        BasicBlock *VMInterpreter_bb = BasicBlock::Create(
            context, "VMInterpreter", &F, VMInterpreterbody_bb);

        // First create the block of the initialization vector table
        BasicBlock *entry_bb =
            BasicBlock::Create(context, "entry", &F, VMInterpreter_bb);

        srand(time(0));
        // PC vector table
        std::vector<ConstantInt *> switch_elems;
        std::vector<Constant *> const_array_elems;
        // In order to solve the problem of variable life cycle, apply for a
        // variable for each instruction
        std::vector<Value *> var_declare;
        size_t split_bb_num = 0;

        // Add all instruction to separate blocks
        while (!originBB.empty()) {
            BasicBlock::iterator first_insn = originBB.begin();
            unsigned int insn_opcode = first_insn->getOpcode();
            if (insn_opcode == Instruction::Alloca)
            // Variable declaration is not confusing, put it in entry
            {
                fn_new_entry_bb->getInstList().splice(
                    fn_new_entry_bb->end(), originBB.getInstList(), first_insn);

                continue;
            }

            // For the instruction that jumps to PHINODE, do not cut it into
            // a separate bb, and put it into the bb of the previous
            // instruction
            if (isPHINodeBranchInst(*first_insn)) {
                BasicBlock *bb = *handlerbb_list.rbegin();

                // Remove the last added br
                bb->getTerminator()->eraseFromParent();
                // Add this br to previous block
                bb->getInstList().splice(bb->end(), originBB.getInstList(),
                                         first_insn);
                bb->replaceSuccessorsPhiUsesWith(&originBB, bb);
            } else {
                ++split_bb_num;
                auto block_name = string_format("VMInterpreterHandler_%ld",
                                                count_VMInterpreterHandler);
                ++count_VMInterpreterHandler;
                BasicBlock *new_bb = BasicBlock::Create(
                    context, block_name.c_str(), &F, &originBB);

                new_bb->getInstList().splice(
                    new_bb->end(), originBB.getInstList(), first_insn);

                if (!new_bb->begin()->isTerminator()) {
                    builder.SetInsertPoint(new_bb, new_bb->end());
                    builder.CreateBr(VMInterpreterbody_bb);
                }

                int code = rand();
                switch_elems.push_back(
                    ConstantInt::get(Type::getInt32Ty(context), code));
                const_array_elems.push_back(
                    ConstantInt::get(Type::getInt32Ty(context), code));
                handlerbb_list.push_back(new_bb);
                all_dup_handler.push_back(new_bb);
            }
        }

        to_earse_bbs.push_back(&originBB);

        ArrayType *array_type =
            ArrayType::get(Type::getInt32Ty(context), split_bb_num);
        GlobalVariable *opcodes = new llvm::GlobalVariable(
            *F.getParent(),
            /*Type=*/array_type,
            /*isConstant=*/true,
            /*Linkage=*/llvm::GlobalValue::PrivateLinkage,
            /*Initializer=*/0,  // has initializer, specified below
            /*Name=*/"opcodes");
        opcodes->setAlignment(MaybeAlign(4));
        opcodes->setInitializer(
            ConstantArray::get(array_type, const_array_elems));
        if (config.is_out_debug()) {
            errs() << *opcodes << "\n";
        }

        // alloca is concentrated at the entrance
        // fn_new_entry_bb: first block of the function
        // entry_bb: new entry block of this block only
        builder.SetInsertPoint(fn_new_entry_bb, fn_new_entry_bb->end());
        Value *opcodesPtr = builder.CreateAlloca(Type::getInt32PtrTy(context),
                                                 nullptr, "opcodesPtr");
        Value *i_alloc =
            builder.CreateAlloca(Type::getInt32Ty(context), nullptr, "i_alloc");

        // entry
        builder.SetInsertPoint(entry_bb, entry_bb->end());
        Value *opcodesGVCast = builder.CreateBitCast(
            opcodes, Type::getInt32PtrTy(context), "opcodesGVCast");
        builder.CreateStore(opcodesGVCast, opcodesPtr);
        builder.CreateBr(VMInterpreter_bb);
        // Replace originBB predecessor with entry_bb
        originBB.replaceAllUsesWith(entry_bb);

        // VMInterpreter
        builder.SetInsertPoint(VMInterpreter_bb);

        // Create variable i and initialize it to 0
        Value *con0 = ConstantInt::get(Type::getInt32Ty(context), 0);
        builder.CreateStore(con0, i_alloc);
        builder.CreateBr(VMInterpreterbody_bb);

        // VMInterperterBody
        builder.SetInsertPoint(VMInterpreterbody_bb);
        Value *loaded_i =
            builder.CreateLoad(Type::getInt32Ty(context), i_alloc, "load_i");
        Value *con1 = ConstantInt::get(Type::getInt32Ty(context), 1);
        Value *increased_i = builder.CreateAdd(loaded_i, con1, "increased_i");
        builder.CreateStore(increased_i, i_alloc);
        Value *loadedOpcodePtr = builder.CreateLoad(
            Type::getInt32PtrTy(context), opcodesPtr, "loadedOpcodePtr");
        Value *opcodesIdx = builder.CreateGEP(
            Type::getInt32Ty(context), loadedOpcodePtr, loaded_i, "opcodesIdx");
        Value *loadedOpcode = builder.CreateLoad(Type::getInt32Ty(context),
                                                 opcodesIdx, "loadedOpcode");

        // create switch statement
        SwitchInst *switch_inst = builder.CreateSwitch(
            loadedOpcode, VMInterpreterbody_bb, split_bb_num);
        for (size_t i = 0; i < split_bb_num; ++i) {
            switch_inst->addCase(switch_elems[i], handlerbb_list[i]);
        }

        // errs() << *entry_bb << "\n";
        // errs() << *VMInterpreter_bb << "\n";
        // errs() << *VMInterpreterbody_bb << "\n";
    }

    // This loop is to duplicate the current instruction
    // to a stack variable and replace all uses with the stack variables.

    set<string> handled_phinode;

    for (size_t i = 0; i < all_dup_handler.size(); ++i) {
        BasicBlock *bb = all_dup_handler[i];

        string bb_name(bb->getName());

        for (Instruction &insn : *bb) {
            llvm::Value *returnval = llvm::cast<llvm::Value>(&insn);

            // There is a reference below the instruction return value
            if (!returnval->hasNUsesOrMore(1)) {
                continue;
            }

            // skip instruction that we added to load value from replace
            if (all_dup_load.find(get_hash(returnval)) != all_dup_load.end()) {
                continue;
            }

            std::vector<BasicBlock *> returnval_users;
            std::vector<PHINode *> phinode_users;

            // find all bock that have instruction that use this
            // instruction
            for (auto user : returnval->users()) {
                // find the instruction referencing this variable
                Instruction *insn = llvm::cast<Instruction>(user);
                BasicBlock *that_bb = insn->getParent();

                if (isa<PHINode>(insn)) {
                    BasicBlock *phi_bb;
                    auto phi_ins = cast<PHINode>(insn);
                    size_t idx_bb;
                    if (!phinode_get_block_of_value(returnval, phi_ins, phi_bb,
                                                    idx_bb)) {
                        outs() << "phi: " << *phi_ins << "\n";
                        outs() << "value: " << *returnval << "\n";
                        assert(false &&
                               "can't find block of this value from phi");
                        continue;
                    }
                    // handle phi node
                    if (handled_phinode.find(get_hash(insn, idx_bb)) ==
                        handled_phinode.end()) {
                        // only handle once for a node index
                        phinode_users.push_back(cast<PHINode>(insn));
                        handled_phinode.insert(get_hash(insn, idx_bb));

                        outs() << " add phi hash " << get_hash(insn, idx_bb)
                               << " phi user block name "
                               << phi_ins->getParent()->getName() << " bb_name "
                               << bb_name << " phi " << insn << "\n";
                    }
                    continue;
                }

                // Add the user instruction's block to our duplicate
                // list

                // Find references that are not in the current
                // bb
                if (that_bb != bb) {
                    returnval_users.push_back(that_bb);
                }
            }
            if (!returnval_users.empty()) {
                duplicate_normal_ins(returnval, returnval_users, builder,
                                     fn_new_entry_bb, bb, all_dup_handler,
                                     replace_map, all_dup_load, all_dup_store);
            }

            if (!phinode_users.empty()) {
                duplicate_phinode_ins(returnval, phinode_users, builder,
                                      fn_new_entry_bb, bb, all_dup_handler,
                                      replace_map, all_dup_load, all_dup_store);
            }
        }
    }

    for (auto &bb : to_earse_bbs) {
        bb->eraseFromParent();
    }

    // String the new entry in
    {
        IRBuilder<> builder(F.getContext());
        builder.SetInsertPoint(fn_new_entry_bb, fn_new_entry_bb->end());
        builder.CreateBr(fn_new_entry_bb->getNextNode());
    }

    std::vector<BasicBlock *> all_bbs;
    for (BasicBlock &bb : F) {
        all_bbs.push_back(&bb);
    }

    // obfuscate unconditional jump block with opaque predicate
    for (auto *bb : all_bbs) {
        if (rand() % 2 == 0) {
            if (bb->getTerminator()->getNumSuccessors() == 1) {
                insert_opaque_predicate(bb, bb->getSingleSuccessor());
            }
        }
    }

    if (this->config.is_out_debug()) {
        outs() << F.getName()
               << " =================== After =======================\n"
               << F << "\n";
    }
    return true;
}

void MyVMObfuscation::duplicate_phinode_ins(
    llvm::Value *returnval, const std::vector<PHINode *> &phinode_users,
    IRBuilder<> &builder, BasicBlock *fn_new_entry_bb,
    BasicBlock *current_ins_bb,
    const std::vector<BasicBlock *> &all_dup_handler,
    std::unordered_map<std::string, ReplaceItem> &replace_map,
    std::set<std::string> &all_dup_load, std::set<std::string> &all_dup_store) {
    Value *tmp_ptr;

    // check if replace var is already created before by duplicate_normal_ins
    auto found = replace_map.find(get_hash(returnval));
    if (found != replace_map.end()) {
        ReplaceItem &ri = found->second;
        tmp_ptr = ri.replace;
    } else {
        // declare a new variable in entry that store the
        // instruction result
        builder.SetInsertPoint(fn_new_entry_bb, fn_new_entry_bb->end());
        tmp_ptr = add_new_replace(returnval, replace_map, builder);

        // Assign this variable in new_bb,
        // and replace all uses of the return value of this
        // instruction with this variable
        BasicBlock::iterator p = current_ins_bb->end();
        --p;
        builder.SetInsertPoint(current_ins_bb, p);
        auto store_ins = builder.CreateStore(returnval, tmp_ptr);
        all_dup_store.insert(get_hash(store_ins));
    }

    for (PHINode *phi_ins : phinode_users) {
        // get block of current dup value from phi node
        for (size_t i = 0; i < phi_ins->getNumIncomingValues(); ++i) {
            if (phi_ins->getIncomingValue(i) == returnval) {
                BasicBlock *block_of_value = phi_ins->getIncomingBlock(i);
                size_t block_idx = i;

                // load the replace value
                BasicBlock::iterator p = block_of_value->end();
                --p;
                builder.SetInsertPoint(block_of_value, p);
                Value *replace =
                    builder.CreateLoad(returnval->getType(), tmp_ptr);

                // Add to set so we can skip it when we create dup next time
                all_dup_load.insert(get_hash(replace));
                // set incoming for this phi
                phi_ins->setIncomingValue(block_idx, replace);
            }
        }
    }
}

bool MyVMObfuscation::phinode_get_block_of_value(Value *val, PHINode *p,
                                                 BasicBlock *&res,
                                                 size_t &idx_of_block) {
    for (size_t i = 0; i < p->getNumIncomingValues(); ++i) {
        if (p->getIncomingValue(i) == val) {
            res = p->getIncomingBlock(i);
            idx_of_block = i;
            return true;
        }
    }
    return false;
}

Value *MyVMObfuscation::add_new_replace(
    Value *org_val, unordered_map<string, ReplaceItem> &replace_map,
    IRBuilder<> &builder) {
    auto tmp_val = builder.CreateAlloca(org_val->getType(), nullptr, "replace");

    ReplaceItem ri;
    ri.value = org_val;
    ri.replace = tmp_val;
    replace_map.insert(make_pair(get_hash(org_val), ri));
    return tmp_val;
}

void MyVMObfuscation::duplicate_normal_ins(
    llvm::Value *returnval, const std::vector<BasicBlock *> &returnval_users,
    IRBuilder<> &builder, BasicBlock *fn_new_entry_bb,
    BasicBlock *current_ins_bb,
    const std::vector<BasicBlock *> &all_dup_handler,
    unordered_map<string, ReplaceItem> &replace_map,
    std::set<std::string> &all_dup_load, std::set<std::string> &all_dup_store) {
    // declare a new variable in entry that store the
    // instruction result

    Value *tmp_ptr;
    auto found = replace_map.find(get_hash(returnval));
    if (found != replace_map.end()) {
        ReplaceItem &ri = found->second;
        tmp_ptr = ri.replace;
    } else {
        builder.SetInsertPoint(fn_new_entry_bb, fn_new_entry_bb->end());
        tmp_ptr = add_new_replace(returnval, replace_map, builder);
        // Assign this variable in new_bb,
        // and replace all uses of the return value of this
        // instruction with this variable
        BasicBlock::iterator p = current_ins_bb->end();
        --p;
        builder.SetInsertPoint(current_ins_bb, p);
        auto store_ins = builder.CreateStore(returnval, tmp_ptr);
        all_dup_store.insert(get_hash(store_ins));
    }

    // go through the list of block that use the
    // instruction
    for (BasicBlock *ele_bb : returnval_users) {
        auto insert_point = ele_bb->begin();

        while (isa<LandingPadInst>(&*insert_point)) {
            ++insert_point;
        }

        while (isa<PHINode>(&*insert_point)) {
            ++insert_point;
        }

        builder.SetInsertPoint(ele_bb, insert_point);
        Value *replace = builder.CreateLoad(returnval->getType(), tmp_ptr);
        all_dup_load.insert(get_hash(replace));

        returnval->replaceUsesWithIf(replace, [this, all_dup_load,
                                               all_dup_store, ele_bb](Use &U) {
            auto *I = dyn_cast<Instruction>(U.getUser());
            if (I == nullptr) return true;
            // do not replace phi node;
            if (isa<PHINode>(I)) {
                return false;
            }
            // do not replace our load instruction
            if (all_dup_load.find(this->get_hash(I)) != all_dup_load.end()) {
                return false;
            }
            if (all_dup_store.find(this->get_hash(I)) != all_dup_store.end()) {
                return false;
            }
            if (I->getParent() != ele_bb) {
                return false;
            }
            return true;
        });
    }
}

string MyVMObfuscation::get_hash(Value *v1, size_t idx) {
    return string_format("%lx_%lx", v1, idx);
}

string MyVMObfuscation::get_hash(Value *v) { return string_format("%lx", v); }

void MyVMObfuscation::init() { config.add_config("LIGHTVM_OBF"); }

PreservedAnalyses LightVM::run(Function &F, FunctionAnalysisManager &AM) {
    std::string func_name(F.getName());
    std::string mod_name(F.getParent()->getName());
    if (!config.is_module_match(mod_name) ||
        !config.is_function_match(func_name)) {
        return PreservedAnalyses::all();
    }
    errs() << "LightVM " << mod_name << ":" << func_name << "\n";
    if (!runOnFunction(F)) {
        return PreservedAnalyses::all();
    } else {
        return PreservedAnalyses::none();
    }
}
}  // namespace llvm
