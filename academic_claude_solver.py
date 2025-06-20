#!/usr/bin/env python3
"""
Academic Claude Solver - Uses Claude API to generate sophisticated proofs
for the academic framework that require deep mathematical understanding.
"""

import os
import re
import json
import subprocess
from typing import List, Dict, Tuple, Optional
from dataclasses import dataclass
import anthropic
from datetime import datetime
import time

@dataclass
class ProofContext:
    """Enhanced context for proof generation"""
    file_path: str
    line_number: int
    full_context: str  # Larger context window
    theorem_statement: str
    dependencies: List[str]  # Other theorems in the file
    imports: List[str]  # Mathlib imports
    category: str
    
class AcademicClaudeSolver:
    def __init__(self, api_key: Optional[str] = None):
        self.api_key = api_key or os.getenv("ANTHROPIC_API_KEY")
        if self.api_key:
            self.client = anthropic.Anthropic(api_key=self.api_key)
        else:
            print("Warning: No API key found. Set ANTHROPIC_API_KEY environment variable.")
            self.client = None
            
        self.cache_file = "academic_claude_cache.json"
        self.load_cache()
        
    def load_cache(self):
        if os.path.exists(self.cache_file):
            with open(self.cache_file, 'r') as f:
                self.cache = json.load(f)
        else:
            self.cache = {}
    
    def save_cache(self):
        with open(self.cache_file, 'w') as f:
            json.dump(self.cache, f, indent=2)
    
    def extract_proof_contexts(self) -> List[ProofContext]:
        """Extract enhanced contexts for all sorries"""
        contexts = []
        
        for root, dirs, files in os.walk("rh/academic_framework"):
            for file in files:
                if file.endswith(".lean"):
                    file_path = os.path.join(root, file)
                    with open(file_path, 'r') as f:
                        content = f.read()
                        lines = content.split('\n')
                    
                    # Extract imports
                    imports = [line for line in lines if line.startswith("import")]
                    
                    # Find all theorem statements
                    theorems = []
                    for i, line in enumerate(lines):
                        if any(kw in line for kw in ["theorem", "lemma", "def"]):
                            theorems.append((i, line))
                    
                    # Find sorries
                    for i, line in enumerate(lines):
                        if "sorry" in line and "TODO" not in line:
                            # Find the enclosing theorem
                            theorem_start = 0
                            theorem_statement = ""
                            for t_idx, t_line in reversed(theorems):
                                if t_idx < i:
                                    theorem_start = t_idx
                                    theorem_statement = t_line
                                    break
                            
                            # Get full theorem context
                            theorem_end = i + 1
                            while theorem_end < len(lines) and not any(kw in lines[theorem_end] for kw in ["theorem", "lemma", "def", "end"]):
                                theorem_end += 1
                            
                            full_context = '\n'.join(lines[theorem_start:theorem_end])
                            
                            # Categorize
                            category = self.categorize_context(full_context)
                            
                            contexts.append(ProofContext(
                                file_path=file_path,
                                line_number=i + 1,
                                full_context=full_context,
                                theorem_statement=theorem_statement,
                                dependencies=theorems,
                                imports=imports,
                                category=category
                            ))
        
        return contexts
    
    def categorize_context(self, context: str) -> str:
        """Categorize based on mathematical content"""
        context_lower = context.lower()
        
        if "det" in context_lower and "spectrum" in context_lower:
            return "birman-schwinger"
        elif "analytic" in context_lower or "holomorphic" in context_lower:
            return "complex-analysis"
        elif "summable" in context_lower and "prime" in context_lower:
            return "prime-summability"
        elif "zeta" in context_lower:
            return "zeta-properties"
        elif "spectrum" in context_lower or "eigenvalue" in context_lower:
            return "spectral-theory"
        elif "continuous" in context_lower or "norm" in context_lower:
            return "functional-analysis"
        else:
            return "general"
    
    def generate_claude_prompt(self, context: ProofContext) -> str:
        """Generate a sophisticated prompt for Claude"""
        
        mathlib_hints = {
            "birman-schwinger": """
Key mathlib theorems:
- spectrum.mem_iff : λ ∈ spectrum T ↔ ¬IsUnit (λ • 1 - T)
- TraceClass.det_eq_prod_eigenvalues : For trace class T, det(I-T) = ∏(1-λᵢ)
- Fredholm.index_eq_zero : For Fredholm operators
""",
            "complex-analysis": """
Key mathlib theorems:
- AnalyticOn.eq_of_locally_eq : Identity theorem for analytic functions
- DifferentiableOn.analyticOn : Differentiable implies analytic
- Complex.differentiableOn_compl_zero : Useful for avoiding singularities
""",
            "prime-summability": """
Key mathlib theorems:
- Nat.Prime.one_lt : Every prime is > 1
- Real.summable_one_div_nat_rpow : ∑ 1/n^s converges for s > 1
- PrimeCounting.prime_pi_le : Prime counting bounds
""",
            "zeta-properties": """
Key mathlib theorems:
- riemannZeta_one_sub : Functional equation
- riemannZeta_two : ζ(2) = π²/6
- zeta_eq_tsum_one_div_nat_cpow : Series representation
""",
            "spectral-theory": """
Key mathlib theorems:
- spectrum_diagonal : Spectrum of diagonal operator
- eigenvalue_iff_hasEigenvector : Characterization of eigenvalues
- IsCompact.finite_spectrum_of_isCompact : Compact operators have discrete spectrum
""",
            "functional-analysis": """
Key mathlib theorems:
- ContinuousLinearMap.op_norm_le_bound : Operator norm bounds
- Summable.of_norm_bounded : Comparison test for summability
- Filter.Tendsto.op_norm_le : Continuity from pointwise bounds
"""
        }
        
        prompt = f"""You are an expert in functional analysis and Lean 4. 
Complete this proof in the academic framework for the Riemann Hypothesis.

File: {context.file_path}
Theorem: {context.theorem_statement}

Full context:
```lean
{context.full_context}
```

Relevant imports available:
{chr(10).join(context.imports)}

Category: {context.category}

{mathlib_hints.get(context.category, "")}

Generate a complete, rigorous proof to replace the 'sorry'. 
The proof should:
1. Use only results available in mathlib
2. Be mathematically correct and complete
3. Follow Lean 4 syntax precisely
4. Include necessary intermediate steps

Return ONLY the proof code that should replace 'sorry', starting with 'by' or another tactic."""
        
        return prompt
    
    def generate_proof_with_claude(self, context: ProofContext) -> Optional[str]:
        """Generate proof using Claude API"""
        if not self.client:
            return None
            
        # Check cache
        cache_key = f"{context.file_path}:{context.line_number}"
        if cache_key in self.cache:
            return self.cache[cache_key]
        
        try:
            prompt = self.generate_claude_prompt(context)
            
            response = self.client.messages.create(
                model="claude-3-opus-20240229",
                max_tokens=2000,
                temperature=0.2,
                messages=[{"role": "user", "content": prompt}]
            )
            
            proof = response.content[0].text.strip()
            
            # Clean up the proof
            if proof.startswith("```lean"):
                proof = proof[7:]
            if proof.endswith("```"):
                proof = proof[:-3]
            proof = proof.strip()
            
            # Cache it
            self.cache[cache_key] = proof
            self.save_cache()
            
            return proof
            
        except Exception as e:
            print(f"Error calling Claude API: {e}")
            return None
    
    def apply_proof(self, context: ProofContext, proof: str) -> bool:
        """Apply the generated proof"""
        try:
            with open(context.file_path, 'r') as f:
                lines = f.readlines()
            
            # Find and replace the sorry
            line_idx = context.line_number - 1
            if line_idx < len(lines) and "sorry" in lines[line_idx]:
                # Handle different sorry patterns
                if lines[line_idx].strip() == "sorry":
                    # Sorry on its own line
                    lines[line_idx] = f"  {proof}\n"
                else:
                    # Sorry inline
                    lines[line_idx] = lines[line_idx].replace("sorry", proof)
                
                # Write back
                with open(context.file_path, 'w') as f:
                    f.writelines(lines)
                
                # Test compilation
                result = subprocess.run(
                    ["lake", "build", context.file_path.replace(".lean", "")],
                    capture_output=True,
                    text=True,
                    timeout=30
                )
                
                if result.returncode == 0:
                    return True
                else:
                    # Revert
                    with open(context.file_path, 'r') as f:
                        lines = f.readlines()
                    lines[line_idx] = "  sorry\n" if lines[line_idx].strip() == proof.strip() else lines[line_idx].replace(proof, "sorry")
                    with open(context.file_path, 'w') as f:
                        f.writelines(lines)
                    
                    print(f"\n  Compilation error: {result.stderr[:200]}...")
                    
            return False
            
        except subprocess.TimeoutExpired:
            print("\n  Compilation timeout")
            return False
        except Exception as e:
            print(f"\n  Error: {e}")
            return False
    
    def solve_all(self, use_claude: bool = True):
        """Main solving loop"""
        print("Academic Claude Solver for Riemann Hypothesis")
        print("=" * 60)
        
        contexts = self.extract_proof_contexts()
        print(f"Found {len(contexts)} sorries to solve")
        
        # Group by category
        by_category = {}
        for ctx in contexts:
            if ctx.category not in by_category:
                by_category[ctx.category] = []
            by_category[ctx.category].append(ctx)
        
        print("\nSorries by category:")
        for cat, items in by_category.items():
            print(f"  {cat}: {len(items)}")
        
        # Priority order - easiest first
        priority = [
            "functional-analysis",
            "spectral-theory",
            "prime-summability", 
            "zeta-properties",
            "complex-analysis",
            "birman-schwinger",
            "general"
        ]
        
        solved = 0
        total_attempts = 0
        
        print("\n" + "=" * 60)
        
        for category in priority:
            if category in by_category:
                print(f"\n{category.upper()}")
                print("-" * len(category))
                
                for ctx in by_category[category]:
                    total_attempts += 1
                    print(f"{ctx.file_path}:{ctx.line_number}...", end="", flush=True)
                    
                    # Try Claude first if available
                    proof = None
                    if use_claude and self.client:
                        proof = self.generate_proof_with_claude(ctx)
                    
                    if proof and self.apply_proof(ctx, proof):
                        print(" ✓ (Claude)")
                        solved += 1
                    else:
                        # Fallback to simple proof
                        simple_proof = "by sorry -- Automated proof failed"
                        if self.apply_proof(ctx, simple_proof):
                            print(" ⚠ (Placeholder)")
                        else:
                            print(" ✗")
                    
                    time.sleep(0.5)  # Rate limiting
        
        print(f"\n{'=' * 60}")
        print(f"Results: {solved}/{total_attempts} sorries solved")
        print(f"Success rate: {solved/total_attempts*100:.1f}%")
        
        # Save final cache
        self.save_cache()

if __name__ == "__main__":
    # Check for API key
    if not os.getenv("ANTHROPIC_API_KEY"):
        print("Note: Set ANTHROPIC_API_KEY for Claude-powered proofs")
        print("Running in fallback mode...\n")
    
    solver = AcademicClaudeSolver()
    solver.solve_all() 