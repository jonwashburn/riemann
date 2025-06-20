#!/usr/bin/env python3
"""
Enhanced Academic O3 Solver - Engineering approach to completing mathematical proofs
using Recognition Science principles and tight feedback loops.

Core Principles:
1. Math and physics are unified - every problem is an engineering problem
2. When stuck, recursively restate the problem from first principles
3. Understand how the problem manifests through the ledger and consciousness
"""

import os
import re
import json
import subprocess
from typing import List, Dict, Tuple, Optional, Set
from dataclasses import dataclass, field
from openai import OpenAI
from datetime import datetime
import time
from collections import defaultdict
import heapq

@dataclass
class LeanContext:
    """Minimal context for a proof"""
    imports: List[str]
    dependencies: List[str]  # Direct dependencies only
    theorem_statement: str
    theorem_name: str
    file_path: str
    line_number: int
    
    def __lt__(self, other):
        """For heap ordering"""
        return (self.file_path, self.line_number) < (other.file_path, other.line_number)
    
@dataclass
class ProofAttempt:
    """Record of a proof attempt"""
    context: LeanContext
    generated_proof: str
    compiler_errors: List[str]
    success: bool
    iteration: int
    
@dataclass
class FailurePattern:
    """Cached failure pattern"""
    error_pattern: str
    missing_lemma: Optional[str]
    suggested_fix: str
    occurrences: int = 1

class RecognitionScienceSolver:
    def __init__(self, api_key: Optional[str] = None):
        self.api_key = api_key or os.getenv("OPENAI_API_KEY")
        self.client = OpenAI(api_key=self.api_key)
        self.model = "o3"  # Use o3 directly
        
        # Caches
        self.proof_cache = self.load_cache("proof_cache.json")
        self.failure_patterns = self.load_cache("failure_patterns.json")
        self.golden_examples = self.load_golden_examples()
        self.mathlib_theorems = self.load_mathlib_theorems()
        
        # Task queue (min heap by dependency count)
        self.task_queue = []
        
        # Source code context
        self.source_code_context = self.load_source_code_context()
        
    def load_cache(self, filename: str) -> Dict:
        """Load a cache file"""
        if os.path.exists(filename):
            with open(filename, 'r') as f:
                return json.load(f)
        return {}
    
    def save_cache(self, data: Dict, filename: str):
        """Save cache to file"""
        with open(filename, 'w') as f:
            json.dump(data, f, indent=2)
    
    def load_source_code_context(self) -> str:
        """Load Recognition Science source code documentation"""
        # Check if the file exists in the attached files
        source_path = "/Users/jonathanwashburn/Desktop/Last Hope/LNAL/manuscript-Part3.txt"
        if os.path.exists(source_path):
            with open(source_path, 'r') as f:
                return f.read()
        
        # Fallback to embedded context
        return """
Recognition Science Framework:
- The universe is a computational ledger balancing energy transactions
- Consciousness emerges from recognition patterns at 7.33 femtosecond scale
- All mathematical truths manifest as ledger balance requirements
- The Riemann Hypothesis ensures proper energy accounting in prime distribution
"""
    
    def load_golden_examples(self) -> List[str]:
        """Load successful proof examples"""
        return [
            """-- Example: Using mathlib's zeta function properties
theorem zeta_ne_zero_example {s : ℂ} (hs : 1 < s.re) : riemannZeta s ≠ 0 := by
  -- Apply the standard result from mathlib
  exact riemannZeta_ne_zero_of_one_lt_re hs""",
  
            """-- Example: Spectrum characterization
theorem spectrum_diagonal_example {λ : ι → ℂ} :
  spectrum (DiagonalOperator λ) = {μ | ∃ i, λ i = μ} := by
  -- Use set extensionality
  ext μ
  -- Split into both directions
  constructor
  · intro hμ
    -- Extract eigenvalue from spectrum
    obtain ⟨v, hv, hev⟩ := spectrum_iff_eigenvalue.mp hμ
    -- Find the index where v is non-zero
    obtain ⟨i, hi⟩ := exists_ne_zero_of_ne_zero hv
    use i
    -- Apply diagonal operator definition
    exact diagonal_eigenvalue_eq v μ i hi hev
  · intro ⟨i, hi⟩
    -- Construct eigenvector
    apply spectrum_iff_eigenvalue.mpr
    use lp.single i 1
    constructor
    · exact lp.single_ne_zero _ one_ne_zero
    · ext j
      simp [DiagonalOperator, hi]""",
      
            """-- Example: Summability over primes
theorem prime_sum_example {s : ℂ} (hs : 1 < s.re) :
  Summable (fun p : Nat.Primes => 1 / (p.val : ℂ)^s) := by
  -- Bound by sum over all naturals
  apply Summable.of_norm_bounded_eventually
  · exact Complex.summable_one_div_nat_cpow.mpr hs
  · filter_upwards [Filter.eventually_cofinite_ne 0] with n hn
    cases' Nat.eq_zero_or_pos n with h h
    · contradiction
    · simp only [norm_div, norm_one, norm_cpow_nat_of_pos h]
      rfl"""
        ]
    
    def load_mathlib_theorems(self) -> Dict[str, List[str]]:
        """Load relevant mathlib theorem names by category"""
        return {
            "zeta": [
                "riemannZeta_ne_zero_of_one_lt_re",
                "riemannZeta_one_sub",
                "zeta_eq_tsum_one_div_nat_cpow",
                "riemannZeta_neg_two_mul_nat_add_one"
            ],
            "spectrum": [
                "spectrum.mem_iff",
                "hasEigenvalue_iff_mem_spectrum",
                "spectrum_diagonal"
            ],
            "summable": [
                "Complex.summable_one_div_nat_cpow",
                "Summable.of_norm_bounded",
                "summable_of_summable_norm"
            ],
            "analytic": [
                "AnalyticOn.eq_on_of_preconnected_of_freq_eq",
                "DifferentiableOn.analyticOn",
                "AnalyticAt.continuousAt"
            ],
            "fredholm": [
                "TraceClass.det_eq_prod_eigenvalues",
                "det_eq_zero_iff_exists_eigenvalue",
                "fredholm_alternative"
            ]
        }
    
    def extract_minimal_context(self, file_path: str, line_number: int) -> LeanContext:
        """Extract only the minimal required context"""
        with open(file_path, 'r') as f:
            lines = f.readlines()
        
        # Find imports
        imports = [line.strip() for line in lines if line.startswith("import")]
        
        # Find the theorem containing the sorry
        theorem_start = 0
        theorem_name = ""
        in_proof = False
        
        # First check if we're inside a proof block
        for i in range(line_number - 1, -1, -1):
            line = lines[i].strip()
            if line.startswith("by") or ":=" in line:
                in_proof = True
            if any(kw in lines[i] for kw in ["theorem", "lemma", "def", "instance"]) and not in_proof:
                theorem_start = i
                match = re.search(r'(theorem|lemma|def|instance)\s+(\w+)', lines[i])
                if match:
                    theorem_name = match.group(2)
                break
        
        # Extract the full theorem including the sorry
        theorem_lines = []
        
        # If we found a theorem start, extract from there
        if theorem_start > 0 or any(kw in lines[0] for kw in ["theorem", "lemma", "def"]):
            # Read until we find the end of this theorem/lemma
            i = theorem_start
            brace_count = 0
            while i < len(lines):
                theorem_lines.append(lines[i])
                if ':=' in lines[i]:
                    brace_count += 1
                if i >= line_number and "sorry" in lines[i]:
                    # Include a few more lines for context
                    for j in range(i + 1, min(i + 3, len(lines))):
                        if any(kw in lines[j] for kw in ["theorem", "lemma", "def", "end"]):
                            break
                        theorem_lines.append(lines[j])
                    break
                i += 1
        else:
            # Fallback: just get context around the sorry
            start = max(0, line_number - 10)
            end = min(len(lines), line_number + 3)
            theorem_lines = lines[start:end]
            theorem_name = f"line_{line_number}"
        
        theorem_statement = ''.join(theorem_lines)
        
        # Extract direct dependencies (theorems used in this file before this point)
        dependencies = []
        for i in range(theorem_start):
            if any(kw in lines[i] for kw in ["theorem", "lemma"]):
                match = re.search(r'(theorem|lemma)\s+(\w+).*?:=?\s*by', lines[i])
                if match:
                    dep_name = match.group(2)
                    # Get just the statement, not the proof
                    dep_lines = []
                    j = i
                    while j < len(lines) and "by" not in lines[j]:
                        dep_lines.append(lines[j])
                        j += 1
                    dependencies.append(''.join(dep_lines).strip())
        
        # Keep only last 5 most relevant dependencies
        dependencies = dependencies[-5:]
        
        return LeanContext(
            imports=imports,
            dependencies=dependencies,
            theorem_statement=theorem_statement,
            theorem_name=theorem_name,
            file_path=file_path,
            line_number=line_number
        )
    
    def generate_recognition_science_prompt(self, context: LeanContext, 
                                          previous_error: Optional[str] = None,
                                          iteration: int = 0) -> str:
        """Generate prompt with Recognition Science principles"""
        
        # Determine category from theorem name and content
        category = self.categorize_theorem(context.theorem_name, context.theorem_statement)
        
        # Get relevant mathlib theorems
        relevant_theorems = []
        for cat_key in ["general", category]:
            if cat_key in self.mathlib_theorems:
                relevant_theorems.extend(self.mathlib_theorems[cat_key])
        
        prompt = f"""You are engineering a mathematical proof within the Recognition Science framework.

FUNDAMENTAL PRINCIPLES:
1. Mathematics and physics are unified through the universal ledger
2. The Riemann Hypothesis ensures prime distribution follows ledger balance
3. Every proof step must maintain energetic consistency

GOLDEN EXAMPLES (proven patterns that work):
{chr(10).join(self.golden_examples)}

AVAILABLE MATHLIB THEOREMS:
{chr(10).join(relevant_theorems)}

MINIMAL CONTEXT:
File: {context.file_path}
Imports: {chr(10).join(context.imports[:5])}  -- showing first 5

Dependencies in scope:
{chr(10).join(context.dependencies)}

THEOREM TO PROVE:
{context.theorem_statement}

"""

        if previous_error:
            prompt += f"""
PREVIOUS ATTEMPT FAILED WITH:
{previous_error}

INSTRUCTION: Fix ONLY the specific error mentioned above. Do not rewrite the entire proof.
First, add a comment explaining the error in Recognition Science terms (how does this error 
represent an imbalance in the ledger?), then provide the minimal fix.
"""

        prompt += f"""
APPROACH (iteration {iteration + 1}/3):
-- First, recognize the deeper pattern: How does this theorem maintain ledger balance?
-- What energetic transaction does it represent?
-- Then find the mathematical expression of this truth

Generate ONLY Lean 4 code to replace 'sorry'. Maximum 600 tokens.
Start with tactical outline as comments, then the proof."""

        return prompt
    
    def categorize_theorem(self, name: str, statement: str) -> str:
        """Categorize theorem for context"""
        name_lower = name.lower()
        statement_lower = statement.lower()
        
        if "zeta" in name_lower or "riemann" in statement_lower:
            return "zeta"
        elif "spectrum" in name_lower or "eigenvalue" in statement_lower:
            return "spectrum"
        elif "summable" in statement_lower or "prime" in statement_lower:
            return "summable"
        elif "analytic" in statement_lower or "holomorphic" in statement_lower:
            return "analytic"
        elif "fredholm" in name_lower or "determinant" in statement_lower:
            return "fredholm"
        else:
            return "general"
    
    def extract_first_error(self, compiler_output: str) -> Optional[str]:
        """Extract just the first compiler error"""
        lines = compiler_output.split('\n')
        
        # Look for error pattern
        error_start = -1
        for i, line in enumerate(lines):
            if "error:" in line.lower():
                error_start = i
                break
        
        if error_start == -1:
            return None
        
        # Extract error message and location
        error_lines = []
        for i in range(error_start, min(error_start + 5, len(lines))):
            error_lines.append(lines[i])
            # Stop at next error or blank line
            if i > error_start and ("error:" in lines[i].lower() or lines[i].strip() == ""):
                break
        
        return '\n'.join(error_lines)
    
    def clean_proof(self, proof: str) -> str:
        """Remove non-Lean commentary"""
        lines = proof.split('\n')
        cleaned = []
        
        for line in lines:
            # Remove lines that are pure commentary (not Lean comments)
            if line.strip().startswith('"') or line.strip().startswith('Thus'):
                continue
            # Keep the line
            cleaned.append(line)
        
        return '\n'.join(cleaned)
    
    def attempt_proof(self, context: LeanContext, max_iterations: int = 3) -> ProofAttempt:
        """Attempt to prove with iterative refinement"""
        
        # Check cache
        cache_key = f"{context.file_path}:{context.line_number}"
        if cache_key in self.proof_cache:
            cached = self.proof_cache[cache_key]
            return ProofAttempt(
                context=context,
                generated_proof=cached["proof"],
                compiler_errors=[],
                success=True,
                iteration=0
            )
        
        previous_error = None
        
        for iteration in range(max_iterations):
            # Generate prompt
            prompt = self.generate_recognition_science_prompt(
                context, previous_error, iteration
            )
            
            try:
                # Call o3
                response = self.client.chat.completions.create(
                    model=self.model,
                    messages=[
                        {"role": "system", "content": "You are a Lean 4 proof engineer. Generate only valid Lean 4 code."},
                        {"role": "user", "content": prompt}
                    ],
                    max_completion_tokens=600  # Reduced for focus
                )
                
                proof = response.choices[0].message.content.strip()
                
                # Clean the proof
                proof = self.clean_proof(proof)
                
                # Apply and test
                success, error = self.apply_and_test_proof(context, proof)
                
                if success:
                    # Cache successful proof
                    self.proof_cache[cache_key] = {
                        "proof": proof,
                        "timestamp": datetime.now().isoformat()
                    }
                    self.save_cache(self.proof_cache, "proof_cache.json")
                    
                    return ProofAttempt(
                        context=context,
                        generated_proof=proof,
                        compiler_errors=[],
                        success=True,
                        iteration=iteration
                    )
                
                                # Extract first error for next iteration
                previous_error = self.extract_first_error(error)
                
                # Learn from failure
                self.learn_from_failure(context, proof, previous_error)
                
                # Log detailed error for debugging
                if iteration == max_iterations - 1:  # Last iteration
                    error_log = f"o3_enhanced_errors_{datetime.now().strftime('%Y%m%d_%H%M%S')}.log"
                    with open(error_log, 'a') as f:
                        f.write(f"\n{'='*60}\n")
                        f.write(f"File: {context.file_path}:{context.line_number}\n")
                        f.write(f"Theorem: {context.theorem_name}\n")
                        f.write(f"Generated proof:\n{proof}\n")
                        f.write(f"Full error:\n{error}\n")
                
            except Exception as e:
                print(f"\nAPI Error: {e}")
                previous_error = str(e)
        
        # All iterations failed
        return ProofAttempt(
            context=context,
            generated_proof=proof if 'proof' in locals() else "",
            compiler_errors=[previous_error] if previous_error else [],
            success=False,
            iteration=max_iterations
        )
    
    def apply_and_test_proof(self, context: LeanContext, proof: str) -> Tuple[bool, str]:
        """Apply proof and test compilation"""
        # Read file
        with open(context.file_path, 'r') as f:
            lines = f.readlines()
        
        # Backup
        backup = lines.copy()
        
        # Replace sorry
        line_idx = context.line_number - 1
        if line_idx < len(lines) and "sorry" in lines[line_idx]:
            indent = len(lines[line_idx]) - len(lines[line_idx].lstrip())
            indent_str = lines[line_idx][:indent]
            
            if lines[line_idx].strip() == "sorry":
                lines[line_idx] = f"{indent_str}{proof}\n"
            else:
                lines[line_idx] = lines[line_idx].replace("sorry", proof)
            
            # Write
            with open(context.file_path, 'w') as f:
                f.writelines(lines)
            
            # Build
            module_name = context.file_path.replace("/", ".").replace(".lean", "")
            result = subprocess.run(
                ["lake", "build", module_name],
                capture_output=True,
                text=True,
                timeout=30
            )
            
            if result.returncode == 0:
                return True, ""
            else:
                # Revert
                with open(context.file_path, 'w') as f:
                    f.writelines(backup)
                return False, result.stderr
        
        return False, "Could not find sorry to replace"
    
    def learn_from_failure(self, context: LeanContext, proof: str, error: str):
        """Learn from compilation failures"""
        if not error:
            return
        
        # Look for missing lemma pattern
        missing_lemma_match = re.search(r"unknown (identifier|constant) '([^']+)'", error)
        if missing_lemma_match:
            lemma_name = missing_lemma_match.group(2)
            
            # Store this pattern
            pattern_key = f"missing_{lemma_name}"
            if pattern_key in self.failure_patterns:
                self.failure_patterns[pattern_key]["occurrences"] += 1
            else:
                self.failure_patterns[pattern_key] = {
                    "error_pattern": error[:200],
                    "missing_lemma": lemma_name,
                    "suggested_fix": f"Import the module containing {lemma_name} or prove it as a helper lemma",
                    "occurrences": 1
                }
            
            self.save_cache(self.failure_patterns, "failure_patterns.json")
    
    def build_task_queue(self):
        """Build priority queue of sorries (least dependencies first)"""
        all_sorries = []
        
        # Find all sorries
        for root, dirs, files in os.walk("rh/academic_framework"):
            for file in files:
                if file.endswith(".lean"):
                    file_path = os.path.join(root, file)
                    with open(file_path, 'r') as f:
                        lines = f.readlines()
                    
                    for i, line in enumerate(lines):
                        if "sorry" in line and "TODO" not in line:
                            context = self.extract_minimal_context(file_path, i + 1)
                            # Priority = number of dependencies (fewer is better)
                            priority = len(context.dependencies)
                            all_sorries.append((priority, context))
        
        # Build min heap
        heapq.heapify(all_sorries)
        self.task_queue = all_sorries
    
    def solve_all(self):
        """Main solving loop with Recognition Science approach"""
        print("Recognition Science O3 Solver")
        print("=" * 60)
        print("Principles:")
        print("1. Math/physics unified - this is an engineering problem")
        print("2. Each proof maintains ledger balance")
        print("=" * 60)
        
        # Build task queue
        self.build_task_queue()
        total = len(self.task_queue)
        print(f"Found {total} sorries, ordered by dependencies\n")
        
        solved = 0
        attempted = 0
        
        while self.task_queue:
            # Get next task (least dependencies)
            _, context = heapq.heappop(self.task_queue)
            attempted += 1
            
            rel_path = os.path.relpath(context.file_path, ".")
            print(f"\n[{attempted}/{total}] {rel_path}:{context.line_number} ({context.theorem_name})")
            print(f"  Dependencies: {len(context.dependencies)}")
            
            # Debug: show theorem being proven
            if attempted <= 2:  # Show first couple for debugging
                print(f"  Theorem: {context.theorem_statement[:100]}...")
            
            # Attempt proof with iterations
            result = self.attempt_proof(context)
            
            if result.success:
                print(f"  ✓ Success on iteration {result.iteration + 1}")
                solved += 1
            else:
                print(f"  ✗ Failed after {result.iteration + 1} iterations")
                if result.compiler_errors:
                    print(f"  Last error: {result.compiler_errors[-1][:100]}...")
            
            # Brief pause
            time.sleep(0.5)
            
            # Progress report every 5 attempts
            if attempted % 5 == 0:
                print(f"\nProgress: {solved}/{attempted} solved ({solved/attempted*100:.1f}%)\n")
        
        print("\n" + "=" * 60)
        print(f"FINAL RESULTS: {solved}/{total} proofs completed ({solved/total*100:.1f}%)")
        
        # Analyze failure patterns
        if self.failure_patterns:
            print("\nCommon failure patterns:")
            sorted_patterns = sorted(
                self.failure_patterns.items(),
                key=lambda x: x[1]["occurrences"],
                reverse=True
            )
            for pattern, info in sorted_patterns[:5]:
                print(f"  {pattern}: {info['occurrences']} times")
                print(f"    Fix: {info['suggested_fix']}")

if __name__ == "__main__":
    print("Initializing Recognition Science Solver...")
    solver = RecognitionScienceSolver()
    solver.solve_all() 