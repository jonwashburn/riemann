#!/usr/bin/env python3
"""
Academic O3 Solver - Uses OpenAI's o3/o3-pro model to solve complex mathematical proofs
in the academic framework for the Riemann Hypothesis.
"""

import os
import re
import json
import subprocess
from typing import List, Dict, Tuple, Optional
from dataclasses import dataclass
from openai import OpenAI
from datetime import datetime
import time

@dataclass
class ProofContext:
    """Enhanced context for proof generation"""
    file_path: str
    line_number: int
    full_context: str
    theorem_statement: str
    theorem_name: str
    dependencies: List[str]
    imports: List[str]
    category: str
    file_content: str  # Full file for maximum context

class AcademicO3Solver:
    def __init__(self, api_key: Optional[str] = None):
        self.api_key = api_key or os.getenv("OPENAI_API_KEY")
        self.client = OpenAI(api_key=self.api_key)
        
        # Try o3-pro first, fall back to o3
        self.models = ["o3-pro", "o3"]
        self.current_model = None
        
        self.cache_file = "academic_o3_cache.json"
        self.load_cache()
        
        # Load mathlib context
        self.mathlib_context = self.load_mathlib_context()
        
    def load_cache(self):
        if os.path.exists(self.cache_file):
            with open(self.cache_file, 'r') as f:
                self.cache = json.load(f)
        else:
            self.cache = {}
    
    def save_cache(self):
        with open(self.cache_file, 'w') as f:
            json.dump(self.cache, f, indent=2)
    
    def load_mathlib_context(self) -> Dict[str, str]:
        """Load relevant mathlib theorem statements"""
        context = {
            "spectrum": """
-- From mathlib: Analysis.InnerProductSpace.Spectrum
theorem spectrum.mem_iff {T : E →L[𝕜] E} : λ ∈ spectrum 𝕜 T ↔ ¬IsUnit (λ • 1 - T)

-- From mathlib: LinearAlgebra.Eigenspace.Basic  
theorem hasEigenvalue_iff_mem_spectrum : T.HasEigenvalue μ ↔ μ ∈ spectrum 𝕜 T
""",
            "fredholm": """
-- Fredholm determinant theory
theorem TraceClass.det_eq_prod_eigenvalues {T : E →L[𝕜] E} [TraceClass T] :
  det (1 - T) = ∏' i, (1 - eigenvalues T i)

-- Birman-Schwinger principle
theorem birman_schwinger {T : E →L[𝕜] E} [TraceClass T] :
  det₂ (1 - T) = 0 ↔ 1 ∈ spectrum 𝕜 T
""",
            "analytic": """
-- From mathlib: Analysis.Analytic.IsolatedZeros
theorem AnalyticOn.eq_on_of_preconnected_of_freq_eq {f g : ℂ → ℂ} {s : Set ℂ} 
  (hf : AnalyticOn ℂ f s) (hg : AnalyticOn ℂ g s) (hs : IsPreconnected s) 
  {z₀ : ℂ} (hz₀ : z₀ ∈ s) (hfg : ∃ᶠ z in 𝓝[s] z₀, f z = g z) : 
  ∀ z ∈ s, f z = g z
""",
            "zeta": """
-- From mathlib: NumberTheory.LSeries.RiemannZeta
theorem riemannZeta_one_sub (s : ℂ) (hs : ∀ n : ℕ, s ≠ -n) (hs' : s ≠ 1) :
  riemannZeta (1 - s) = 2 * (2 * π)^(-s) * Gamma s * cos (π * s / 2) * riemannZeta s

theorem zeta_eq_tsum_one_div_nat_cpow {s : ℂ} (hs : 1 < re s) :
  riemannZeta s = ∑' n : ℕ, 1 / (n : ℂ) ^ s

theorem riemannZeta_ne_zero {s : ℂ} (hs : 1 < re s) : riemannZeta s ≠ 0
""",
            "summable": """
-- From mathlib: Analysis.PSeriesComplex
theorem Complex.summable_one_div_nat_cpow {s : ℂ} : 
  Summable (fun n : ℕ => 1 / (n : ℂ) ^ s) ↔ 1 < re s

-- Prime summability
theorem summable_one_div_prime_cpow {s : ℂ} (hs : 1 < re s) :
  Summable (fun p : Nat.Primes => 1 / (p.val : ℂ) ^ s)
"""
        }
        return context
    
    def extract_proof_contexts(self) -> List[ProofContext]:
        """Extract comprehensive contexts for all sorries"""
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
                    
                    # Find all definitions, lemmas, and theorems
                    declarations = []
                    for i, line in enumerate(lines):
                        if any(kw in line for kw in ["theorem", "lemma", "def", "instance"]):
                            declarations.append((i, line))
                    
                    # Find sorries
                    for i, line in enumerate(lines):
                        if "sorry" in line and "TODO" not in line:
                            # Find enclosing theorem
                            theorem_start = 0
                            theorem_statement = ""
                            theorem_name = ""
                            
                            for d_idx, d_line in reversed(declarations):
                                if d_idx < i:
                                    theorem_start = d_idx
                                    theorem_statement = d_line
                                    # Extract theorem name
                                    match = re.search(r'(theorem|lemma|def|instance)\s+(\w+)', d_line)
                                    if match:
                                        theorem_name = match.group(2)
                                    break
                            
                            # Get full theorem context
                            theorem_end = i + 1
                            # Find the end of the current proof/definition
                            brace_count = 0
                            for j in range(theorem_start, len(lines)):
                                if '{' in lines[j]:
                                    brace_count += lines[j].count('{')
                                if '}' in lines[j]:
                                    brace_count -= lines[j].count('}')
                                if j > i and brace_count == 0:
                                    theorem_end = j + 1
                                    break
                                # Also check for next theorem/lemma
                                if j > i and any(kw in lines[j] for kw in ["theorem", "lemma", "def", "end"]):
                                    theorem_end = j
                                    break
                            
                            full_context = '\n'.join(lines[theorem_start:theorem_end])
                            
                            # Get dependencies (previous theorems in file)
                            deps = []
                            for d_idx, d_line in declarations:
                                if d_idx < theorem_start:
                                    deps.append(d_line.strip())
                            
                            # Categorize
                            category = self.categorize_context(full_context, theorem_name)
                            
                            contexts.append(ProofContext(
                                file_path=file_path,
                                line_number=i + 1,
                                full_context=full_context,
                                theorem_statement=theorem_statement,
                                theorem_name=theorem_name,
                                dependencies=deps[-5:],  # Last 5 dependencies
                                imports=imports,
                                category=category,
                                file_content=content
                            ))
        
        return contexts
    
    def categorize_context(self, context: str, name: str) -> str:
        """Enhanced categorization"""
        context_lower = context.lower()
        name_lower = name.lower()
        
        if "birman" in name_lower or "schwinger" in name_lower or ("det" in context_lower and "spectrum" in context_lower):
            return "birman-schwinger"
        elif "analytic" in name_lower or "holomorphic" in context_lower or "continuation" in name_lower:
            return "analytic-continuation"
        elif "summable" in context_lower and "prime" in context_lower:
            return "prime-summability"
        elif "zeta" in name_lower or "riemann" in context_lower:
            return "zeta-function"
        elif "spectrum" in name_lower or "eigenvalue" in context_lower:
            return "spectral-theory"
        elif "continuous" in context_lower or "norm" in context_lower:
            return "functional-analysis"
        elif "diagonal" in name_lower:
            return "diagonal-operators"
        else:
            return "general"
    
    def generate_o3_prompt(self, context: ProofContext) -> str:
        """Generate an optimized prompt for o3"""
        
        # Get relevant mathlib context
        mathlib_relevant = []
        if context.category == "birman-schwinger":
            mathlib_relevant.append(self.mathlib_context["fredholm"])
            mathlib_relevant.append(self.mathlib_context["spectrum"])
        elif context.category == "analytic-continuation":
            mathlib_relevant.append(self.mathlib_context["analytic"])
        elif context.category in ["zeta-function", "prime-summability"]:
            mathlib_relevant.append(self.mathlib_context["zeta"])
            mathlib_relevant.append(self.mathlib_context["summable"])
        elif context.category == "spectral-theory":
            mathlib_relevant.append(self.mathlib_context["spectrum"])
        
        # Build comprehensive prompt
        prompt = f"""You are an expert mathematician and Lean 4 formalization specialist. Your task is to complete a proof in the academic framework for the Riemann Hypothesis.

CONTEXT:
This is part of a rigorous formalization that decomposes the Recognition Science approach into standard mathematical components. The key insight is that if p^(-s) = 1 for a prime p, then |p^(-s)| = p^(-Re(s)) = 1, forcing Re(s) = 0, which contradicts being in the critical strip 1/2 < Re(s) < 1.

FILE: {context.file_path}
CATEGORY: {context.category}

THEOREM TO PROVE:
{context.theorem_statement}

FULL THEOREM CONTEXT:
```lean
{context.full_context}
```

AVAILABLE IMPORTS:
{chr(10).join(context.imports)}

RECENT DEFINITIONS IN FILE:
{chr(10).join(context.dependencies)}

RELEVANT MATHLIB THEOREMS:
{chr(10).join(mathlib_relevant)}

SPECIFIC INSTRUCTIONS FOR {context.category.upper()}:
"""
        
        # Category-specific guidance
        category_guidance = {
            "birman-schwinger": """
- Use the Birman-Schwinger principle: det₂(I - T) = 0 ↔ 1 ∈ spectrum T
- For diagonal operators, the spectrum is the set of diagonal entries
- Use TraceClass.det_eq_prod_eigenvalues for the product formula
""",
            "analytic-continuation": """
- Use the identity theorem: if two analytic functions agree on a set with accumulation point, they're equal
- The domain {s : 1 < Re(s)} has accumulation points in {s : 1/2 < Re(s) < 1}
- Use AnalyticOn.eq_on_of_preconnected_of_freq_eq from mathlib
""",
            "prime-summability": """
- The sum over primes is bounded by the sum over all naturals
- Use Complex.summable_one_div_nat_cpow for convergence
- For PrimeIndex, establish a bijection with Nat.Primes
""",
            "zeta-function": """
- Use riemannZeta_one_sub for the functional equation
- Use zeta_eq_tsum_one_div_nat_cpow for the series representation
- Remember that ζ has a simple pole at s = 1
""",
            "spectral-theory": """
- For diagonal operators, spectrum = range of diagonal function
- Use hasEigenvalue_iff_mem_spectrum
- The spectrum is exactly the set of eigenvalues
""",
            "diagonal-operators": """
- Diagonal operators are bounded if eigenvalues are bounded
- Use the fact that ‖Tx‖² = ∑ |λᵢ|² |xᵢ|²
- Continuity follows from boundedness
""",
            "functional-analysis": """
- Use standard estimates: ‖AB‖ ≤ ‖A‖ ‖B‖
- For continuity, show the map is bounded
- Use completeness of the target space
"""
        }
        
        prompt += category_guidance.get(context.category, "- Apply standard mathematical reasoning\n- Use available lemmas from imports")
        
        prompt += """

TASK: Generate a complete, rigorous proof to replace the 'sorry'. The proof must:
1. Use only results available in mathlib or previously proven in the file
2. Be mathematically correct and complete
3. Follow Lean 4 syntax precisely
4. Handle all edge cases

Return ONLY the Lean code that should replace 'sorry'. Do not include explanations or comments outside the proof."""
        
        return prompt
    
    def generate_proof_with_o3(self, context: ProofContext) -> Optional[str]:
        """Generate proof using o3/o3-pro"""
        # Check cache
        cache_key = f"{context.file_path}:{context.line_number}:{context.theorem_name}"
        if cache_key in self.cache:
            print(" (cached)", end="")
            return self.cache[cache_key]
        
        # Try each model in order
        for model in self.models:
            try:
                prompt = self.generate_o3_prompt(context)
                
                # Call o3 with correct parameters
                # o3 model has restrictions on parameters
                if model == "o3":
                    response = self.client.chat.completions.create(
                        model=model,
                        messages=[
                            {"role": "system", "content": "You are a Lean 4 proof assistant. Generate only valid Lean 4 code."},
                            {"role": "user", "content": prompt}
                        ],
                        max_completion_tokens=3000  # Only parameter o3 supports
                    )
                else:
                    # o3-pro with full parameters
                    response = self.client.chat.completions.create(
                        model=model,
                        messages=[
                            {"role": "system", "content": "You are a Lean 4 proof assistant. Generate only valid Lean 4 code."},
                            {"role": "user", "content": prompt}
                        ],
                        temperature=0.1,
                        max_completion_tokens=3000,
                        top_p=0.95,
                        frequency_penalty=0.0,
                        presence_penalty=0.0
                    )
                
                # Set current model on success
                if self.current_model is None:
                    self.current_model = model
                    print(f"\nUsing model: {model}\n")
                
                proof = response.choices[0].message.content.strip()
                
                # Clean up the proof
                if proof.startswith("```lean"):
                    proof = proof[7:]
                if proof.endswith("```"):
                    proof = proof[:-3]
                proof = proof.strip()
                
                # Basic validation
                if not proof or proof == "sorry":
                    continue  # Try next model
                
                # Cache successful generation
                self.cache[cache_key] = proof
                self.save_cache()
                
                return proof
                
            except Exception as e:
                if "model" in str(e).lower() and model == "o3-pro":
                    # o3-pro not available, try o3
                    print(f"\n  Note: {model} not available, trying o3...")
                    continue
                else:
                    print(f"\n  API Error with {model}: {e}")
                    continue
        
        return None
    
    def apply_proof(self, context: ProofContext, proof: str) -> bool:
        """Apply and validate the generated proof"""
        try:
            with open(context.file_path, 'r') as f:
                lines = f.readlines()
            
            # Create backup
            backup_lines = lines.copy()
            
            # Find and replace the sorry
            line_idx = context.line_number - 1
            if line_idx < len(lines) and "sorry" in lines[line_idx]:
                # Determine indentation
                indent = len(lines[line_idx]) - len(lines[line_idx].lstrip())
                indent_str = lines[line_idx][:indent]
                
                # Handle different patterns
                if lines[line_idx].strip() == "sorry":
                    # Sorry on its own line - replace with indented proof
                    if proof.startswith("by"):
                        lines[line_idx] = f"{indent_str}{proof}\n"
                    else:
                        lines[line_idx] = f"{indent_str}by\n{indent_str}  {proof}\n"
                else:
                    # Inline sorry
                    lines[line_idx] = lines[line_idx].replace("sorry", proof)
                
                # Write updated file
                with open(context.file_path, 'w') as f:
                    f.writelines(lines)
                
                # Test compilation
                # Build from the project root, not the file directory
                module_name = context.file_path.replace("/", ".").replace(".lean", "")
                if module_name.startswith("rh."):
                    module_name = module_name
                else:
                    module_name = "rh." + module_name.replace("rh/", "")
                
                result = subprocess.run(
                    ["lake", "build", module_name],
                    capture_output=True,
                    text=True,
                    timeout=60,
                    cwd="."  # Always run from project root
                )
                
                if result.returncode == 0:
                    return True
                else:
                    # Revert on failure
                    with open(context.file_path, 'w') as f:
                        f.writelines(backup_lines)
                    
                    # Log error for debugging
                    error_log = f"o3_errors_{datetime.now().strftime('%Y%m%d_%H%M%S')}.log"
                    with open(error_log, 'a') as f:
                        f.write(f"\n{'='*60}\n")
                        f.write(f"File: {context.file_path}:{context.line_number}\n")
                        f.write(f"Theorem: {context.theorem_name}\n")
                        f.write(f"Generated proof:\n{proof}\n")
                        f.write(f"Error:\n{result.stderr}\n")
                    
                    print(f" (see {error_log})", end="")
            
            return False
            
        except subprocess.TimeoutExpired:
            # Revert on timeout
            with open(context.file_path, 'w') as f:
                f.writelines(backup_lines)
            print(" (timeout)", end="")
            return False
        except Exception as e:
            print(f" (error: {e})", end="")
            return False
    
    def solve_all(self):
        """Main solving loop with o3"""
        print("Academic O3 Solver for Riemann Hypothesis")
        print("=" * 60)
        print(f"Available models: {', '.join(self.models)}")
        print("=" * 60)
        
        contexts = self.extract_proof_contexts()
        print(f"Found {len(contexts)} sorries to solve\n")
        
        # Group by category
        by_category = {}
        for ctx in contexts:
            if ctx.category not in by_category:
                by_category[ctx.category] = []
            by_category[ctx.category].append(ctx)
        
        print("Sorries by category:")
        for cat, items in sorted(by_category.items()):
            print(f"  {cat}: {len(items)}")
        
        # Priority order - easiest first to build momentum
        priority = [
            "functional-analysis",
            "diagonal-operators",
            "spectral-theory",
            "prime-summability",
            "zeta-function",
            "analytic-continuation",
            "birman-schwinger",
            "general"
        ]
        
        solved = 0
        total = len(contexts)
        
        print("\n" + "=" * 60)
        print("Starting proof generation...\n")
        
        for category in priority:
            if category in by_category:
                print(f"{category.upper()} ({len(by_category[category])} proofs)")
                print("-" * len(category))
                
                for ctx in by_category[category]:
                    rel_path = os.path.relpath(ctx.file_path, "rh/academic_framework")
                    print(f"  {rel_path}:{ctx.line_number} ({ctx.theorem_name})...", end="", flush=True)
                    
                    # Generate proof with o3
                    proof = self.generate_proof_with_o3(ctx)
                    
                    if proof and self.apply_proof(ctx, proof):
                        print(" ✓")
                        solved += 1
                    else:
                        print(" ✗")
                    
                    # Brief pause to avoid rate limits
                    time.sleep(1)
                
                print()
        
        print("=" * 60)
        print(f"RESULTS: {solved}/{total} proofs completed ({solved/total*100:.1f}%)")
        
        if solved < total:
            print(f"\nRemaining sorries: {total - solved}")
            print("Check error logs for compilation failures.")
        else:
            print("\n🎉 All proofs completed successfully!")
        
        # Save final cache
        self.save_cache()

if __name__ == "__main__":
    print("Initializing O3 solver...")
    solver = AcademicO3Solver()
    solver.solve_all() 