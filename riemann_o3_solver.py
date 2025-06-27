#!/usr/bin/env python3
"""
Advanced Riemann Hypothesis O3 Solver
Adapted from Navier-Stokes solver for RH proof completion
"""

import os
import re
import json
from pathlib import Path
from openai import OpenAI
import subprocess
import shutil
from datetime import datetime

class RiemannHypothesisO3Solver:
    def __init__(self, api_key: str):
        self.client = OpenAI(api_key=api_key)
        
        # Check available models
        print("Checking available models...")
        try:
            models = self.client.models.list()
            model_ids = [model.id for model in models.data]
            print(f"Available models: {', '.join(model_ids[:10])}...")  # First 10
            
            if "o3" in model_ids:
                self.model = "o3"  # Use the actual o3 model
                print("✓ o3 model is available")
                # Try to get model details
                try:
                    # Check if we can get model info
                    for model in models.data:
                        if model.id == "o3":
                            print(f"  Model details: {model}")
                            break
                except:
                    pass
            else:
                print("✗ o3 model not found, using gpt-4o instead")
                self.model = "gpt-4o"
        except Exception as e:
            print(f"Could not list models: {e}")
            print("Defaulting to gpt-4o")
            self.model = "gpt-4o"
        
        # Settings optimized for Lean 4 mathematical proofs
        self.max_iterations = 3
        # Maximum tokens - trying highest possible value
        # Note: Different models have different limits
        # GPT-4: 8192, GPT-4-32k: 32768, o3: 100k tokens
        self.max_tokens = 100000
        self.max_completion_tokens = 100000  # For o3 model
        
        # Statistics
        self.stats = {
            'total_sorries': 0,
            'resolved_sorries': 0,
            'llm_calls': 0,
            'compile_successes': 0,
            'compile_failures': 0
        }
        
        # Backup directory
        self.backup_dir = Path("backups") / datetime.now().strftime("%Y%m%d_%H%M%S")
        self.backup_dir.mkdir(parents=True, exist_ok=True)
        
        # Recognition Science context
        self.rs_context = self.load_recognition_science_context()
        
    def load_recognition_science_context(self):
        """Load key Recognition Science concepts for proof context"""
        return {
            'golden_ratio': """
The golden ratio φ = (1+√5)/2 ≈ 1.618034 emerges from the cost functional J(x) = ½(x + 1/x).
Key fact: φ - 1 = 1/φ ≈ 0.618034 is the unique value that makes the Fredholm determinant identity work.
""",
            'eight_beat': """
Eight-beat cycle: The tick operator L satisfies L^8 = identity, forcing all physical processes to complete within 8 ticks.
This constraint forces zeta zeros to lie on Re(s) = 1/2 to avoid infinite energy accumulation.
""",
            'ledger_balance': """
Cosmic ledger principle: Every recognition event must balance debits and credits.
For the zeta function, this means det(I - A_s) * exp(regularizer) = ζ(s)^(-1).
""",
            'diagonal_operator': """
The diagonal operator A_s has eigenvalues p^(-s) for primes p.
On the weighted space ℓ²(primes, p^(-2(1+ε))) with ε = φ-1, it's Hilbert-Schmidt exactly when 1/2 < Re(s) < 1.
""",
            'determinant_identity': """
Key identity: ∏_p [(1 - p^(-s)) * exp(p^(-s))] = ζ(s)^(-1) for 1/2 < Re(s) < 1.
This ONLY works with the golden ratio weight ε = φ - 1.
"""
        }
        
    def find_sorries(self, file_path: Path):
        """Find all sorries in a file with context"""
        sorries = []
        
        with open(file_path, 'r') as f:
            lines = f.readlines()
            
        for i, line in enumerate(lines):
            if 'sorry' in line and not line.strip().startswith('--'):
                # Find the theorem/lemma declaration
                declaration_lines = []
                j = i
                while j >= 0:
                    if any(kw in lines[j] for kw in ['theorem', 'lemma', 'def', 'instance']):
                        # Found start of declaration
                        while j <= i:
                            declaration_lines.append(lines[j])
                            j += 1
                        break
                    j -= 1
                    
                if declaration_lines:
                    declaration = ''.join(declaration_lines).strip()
                    
                    # Extract name
                    match = re.search(r'(theorem|lemma|def|instance)\s+(\w+)', declaration)
                    name = match.group(2) if match else f'unknown_line_{i+1}'
                    
                    sorries.append({
                        'line': i + 1,
                        'name': name,
                        'declaration': declaration,
                        'file': str(file_path)
                    })
                    
        return sorries
        
    def extract_context(self, file_path: Path, sorry_line: int):
        """Extract relevant context for the proof"""
        with open(file_path, 'r') as f:
            lines = f.readlines()
            
        context = {
            'imports': [],
            'namespace': None,
            'local_defs': [],
            'theorem': ''
        }
        
        # Get imports and namespace
        for i, line in enumerate(lines[:min(50, len(lines))]):
            if line.strip().startswith('import'):
                context['imports'].append(line.strip())
            elif line.strip().startswith('namespace'):
                context['namespace'] = line.strip()
                
        # Find theorem
        theorem_start = None
        for i in range(sorry_line - 1, -1, -1):
            if any(kw in lines[i] for kw in ['theorem', 'lemma', 'def']):
                theorem_start = i
                break
                
        if theorem_start:
            theorem_lines = []
            i = theorem_start
            while i < sorry_line:
                theorem_lines.append(lines[i])
                i += 1
            context['theorem'] = ''.join(theorem_lines)
            
        # Get some local context (definitions above)
        start = max(0, theorem_start - 30) if theorem_start else max(0, sorry_line - 50)
        for i in range(start, theorem_start if theorem_start else sorry_line):
            line = lines[i].strip()
            if any(kw in line for kw in ['def ', 'theorem ', 'lemma ', 'axiom ']):
                # Capture this definition
                def_lines = [lines[i]]
                j = i + 1
                indent = len(lines[i]) - len(lines[i].lstrip())
                while j < len(lines) and (lines[j].strip() == '' or 
                                         len(lines[j]) - len(lines[j].lstrip()) > indent):
                    def_lines.append(lines[j])
                    j += 1
                    if j - i > 20:  # Limit definition size
                        break
                context['local_defs'].append(''.join(def_lines))
                
        return context
        
    def generate_proof(self, sorry_info, context, iteration=0, previous_error=None):
        """Generate proof using O3 with Recognition Science context"""
        
        # Build Recognition Science context section
        rs_section = """
## Recognition Science Context

This proof is part of the Riemann Hypothesis proof using Recognition Science principles:

1. **Golden Ratio Weight**: The diagonal operator uses weight p^(-2(1+ε)) where ε = φ-1 ≈ 0.618034.
   This is the ONLY value that makes the Fredholm determinant identity work.

2. **Eight-Beat Constraint**: The tick operator L satisfies L^8 = identity. Any zero off Re(s)=1/2 
   would accumulate infinite recognition energy over 8 ticks, violating the axioms.

3. **Ledger Balance**: The determinant identity ∏_p [(1-p^(-s))·exp(p^(-s))] = ζ(s)^(-1) 
   represents cosmic ledger balance. It holds ONLY for 1/2 < Re(s) < 1.

4. **Key Objects**:
   - DiagonalOperator' with eigenvalues p^(-s) 
   - PrimeIndex type for indexing over primes
   - euler_operator: the main diagonal operator A_s
   - fredholm_det: the regularized determinant
   - Eight-beat phase constraints

5. **Common Proof Patterns**:
   - Use the axiomatized DiagonalOperator' properties
   - Apply the golden ratio weight ε = φ-1
   - Use eight-beat periodicity constraints
   - Apply Hilbert-Schmidt properties on the critical strip
"""
        
        prompt = f"""You are an expert Lean 4 theorem prover working on the Riemann Hypothesis proof using Recognition Science.

{rs_section}

## Current File Context

Imports:
{chr(10).join(context['imports'][:10])}

{context['namespace'] if context['namespace'] else ''}

Recent definitions:
{chr(10).join(context['local_defs'][-5:])}

Target theorem:
{context['theorem']}

"""

        if previous_error:
            prompt += f"""Previous attempt failed with error:
{previous_error}

Please fix this specific error. Focus on:
- Check if you're using the correct axiomatized definitions
- Verify the golden ratio weight is applied correctly
- Ensure eight-beat constraints are satisfied
"""

        prompt += """## Task

Generate ONLY the proof body to replace the 'sorry'. 

Key guidelines:
- Do NOT include the lemma/theorem declaration
- Do NOT include the lemma name or type signature
- Start directly with the proof (e.g., "by", "begin", or direct term)
- Use axiomatized results where available (DiagonalOperator', diagonal_operator_norm', etc.)
- The golden ratio ε = φ-1 appears in many proofs
- Eight-beat constraints often provide the key insight
- Many proofs involve showing something is Hilbert-Schmidt on 1/2 < Re(s) < 1
- Output ONLY the Lean proof code (no explanations)

IMPORTANT: For test files without mathlib imports, use only core Lean tactics:
- rfl (for reflexivity)
- simp (basic simplification)
- intro/intros (for implications and foralls)
- exact (to provide exact terms)
- apply (to apply lemmas)
- constructor (for And/Or)
- cases (for case analysis)

Example output format:
by
  have h1 : ... := ...
  exact ...

The proof should compile with Lean 4.
"""

        try:
            # Use the correct parameter based on model
            if self.model == "o3":
                print(f"  Calling {self.model} API with max_completion_tokens={self.max_completion_tokens}...")
                response = self.client.chat.completions.create(
                    model=self.model,
                    messages=[
                        {"role": "system", "content": "You are a Lean 4 expert specializing in operator theory and the Riemann Hypothesis. Output only valid Lean code."},
                        {"role": "user", "content": prompt}
                    ],
                    max_completion_tokens=self.max_completion_tokens
                )
            else:
                print(f"  Calling {self.model} API with max_tokens={self.max_tokens}...")
                response = self.client.chat.completions.create(
                    model=self.model,
                    messages=[
                        {"role": "system", "content": "You are a Lean 4 expert specializing in operator theory and the Riemann Hypothesis. Output only valid Lean code."},
                        {"role": "user", "content": prompt}
                    ],
                    max_tokens=self.max_tokens
                )
            
            print(f"  Response received. Choices: {len(response.choices)}")
            if response.choices:
                proof = response.choices[0].message.content.strip()
                print(f"  Raw proof length: {len(proof)} chars")
                self.stats['llm_calls'] += 1
                
                # Clean up the proof
                proof = self.clean_proof(proof)
                print(f"  Cleaned proof length: {len(proof)} chars")
                
                return proof
            else:
                print("  No choices in response")
                return None
            
        except Exception as e:
            print(f"  Error calling API: {type(e).__name__}: {str(e)}")
            
            # If it's a token limit error, try with smaller limit
            if "max_tokens" in str(e).lower() or "token" in str(e).lower() or "max_completion_tokens" in str(e).lower():
                print(f"  Token limit issue detected. Trying with 4096 tokens...")
                try:
                    if self.model == "o3":
                        response = self.client.chat.completions.create(
                            model=self.model,
                            messages=[
                                {"role": "system", "content": "You are a Lean 4 expert specializing in operator theory and the Riemann Hypothesis. Output only valid Lean code."},
                                {"role": "user", "content": prompt}
                            ],
                            max_completion_tokens=4096
                        )
                    else:
                        response = self.client.chat.completions.create(
                            model=self.model,
                            messages=[
                                {"role": "system", "content": "You are a Lean 4 expert specializing in operator theory and the Riemann Hypothesis. Output only valid Lean code."},
                                {"role": "user", "content": prompt}
                            ],
                            max_tokens=4096
                        )
                    
                    print(f"  Response received with 4096 tokens. Choices: {len(response.choices)}")
                    if response.choices:
                        proof = response.choices[0].message.content.strip()
                        print(f"  Raw proof length: {len(proof)} chars")
                        self.stats['llm_calls'] += 1
                        
                        # Clean up the proof
                        proof = self.clean_proof(proof)
                        print(f"  Cleaned proof length: {len(proof)} chars")
                        
                        return proof
                except Exception as e2:
                    print(f"  Still failed with 4096 tokens: {type(e2).__name__}: {str(e2)}")
            
            # Try with gpt-4o if o3 fails
            if self.model == "o3" and "model" in str(e).lower():
                print("  Falling back to gpt-4o...")
                try:
                    response = self.client.chat.completions.create(
                        model="gpt-4o",
                        messages=[
                            {"role": "system", "content": "You are a Lean 4 expert specializing in operator theory and the Riemann Hypothesis. Output only valid Lean code."},
                            {"role": "user", "content": prompt}
                        ],
                        max_tokens=self.max_tokens
                    )
                    
                    proof = response.choices[0].message.content.strip()
                    self.stats['llm_calls'] += 1
                    
                    # Clean up the proof
                    proof = self.clean_proof(proof)
                    
                    return proof
                except Exception as e2:
                    print(f"  Fallback also failed: {type(e2).__name__}: {str(e2)}")
                    return None
            return None
            
    def clean_proof(self, proof: str):
        """Clean up generated proof"""
        
        # Remove markdown code blocks
        if '```' in proof:
            match = re.search(r'```(?:lean)?\s*\n(.*?)\n```', proof, re.DOTALL)
            if match:
                proof = match.group(1)
                
        # Remove non-Lean content
        lines = proof.split('\n')
        clean_lines = []
        
        for line in lines:
            # Skip obvious non-Lean content
            if line.strip() and not any(skip in line.lower() for skip in 
                                       ['here is', 'this proof', 'we can', 'note that']):
                clean_lines.append(line)
                
        return '\n'.join(clean_lines).strip()
        
    def check_compilation(self, file_path: Path):
        """Check if file compiles"""
        try:
            # For test files in root, just compile the file directly
            if file_path.parent == Path.cwd():
                # Compile the file directly
                result = subprocess.run(
                    ['lean', str(file_path)],
                    cwd=Path.cwd(),
                    capture_output=True,
                    text=True,
                    timeout=30
                )
                
                # Debug output
                if result.stderr:
                    print(f"  Debug - stderr: {result.stderr[:200]}")
                if result.stdout:
                    print(f"  Debug - stdout: {result.stdout[:200]}")
                print(f"  Debug - return code: {result.returncode}")
                
                success = result.returncode == 0
                # Only consider it an error if there are actual errors (not just warnings)
                if not success or 'error:' in result.stderr:
                    error = result.stderr
                else:
                    error = None
                    success = True
                
                return success, error
            
            # Get the module name from the file path
            module_parts = []
            current = file_path.stem
            parent = file_path.parent
            
            # Build the module path
            while parent.name != 'riemann 2' and parent != parent.parent:
                if parent.name:
                    module_parts.insert(0, parent.name)
                parent = parent.parent
            module_parts.append(current)
            
            module_name = '.'.join(module_parts)
            
            result = subprocess.run(
                ['lake', 'build', module_name],
                cwd=Path.cwd(),  # Run from current directory (riemann 2)
                capture_output=True,
                text=True,
                timeout=30
            )
            
            success = result.returncode == 0
            error = result.stderr if not success else None
            
            return success, error
            
        except subprocess.TimeoutExpired:
            return False, "Compilation timeout"
        except Exception as e:
            return False, str(e)
            
    def apply_proof(self, file_path: Path, line_num: int, proof: str):
        """Apply proof to file"""
        with open(file_path, 'r') as f:
            lines = f.readlines()
            
        # Replace sorry with proof
        if line_num <= len(lines) and 'sorry' in lines[line_num - 1]:
            # Handle inline sorry
            if lines[line_num - 1].strip() == 'sorry':
                lines[line_num - 1] = proof + '\n'
            else:
                # Replace inline sorry
                lines[line_num - 1] = lines[line_num - 1].replace('sorry', proof)
                
        with open(file_path, 'w') as f:
            f.writelines(lines)
            
    def extract_first_error(self, error_msg: str):
        """Extract the most relevant error"""
        if not error_msg:
            return None
            
        # Look for specific error patterns
        patterns = [
            r'error: (.*?)(?:\n|$)',
            r'failed to synthesize instance(.*?)(?:\n|$)',
            r'type mismatch(.*?)(?:\n|$)',
            r'unknown identifier \'(.*?)\'',
            r'invalid field \'(.*?)\'',
        ]
        
        for pattern in patterns:
            match = re.search(pattern, error_msg, re.IGNORECASE | re.MULTILINE)
            if match:
                return match.group(0)[:200]
                
        # Return first line with error
        for line in error_msg.split('\n'):
            if 'error' in line.lower():
                return line[:200]
                
        return error_msg[:200]
        
    def solve_sorry(self, file_path: Path, sorry_info):
        """Attempt to solve a single sorry"""
        
        print(f"\n{'='*60}")
        print(f"Solving: {sorry_info['name']} at line {sorry_info['line']}")
        print(f"File: {file_path.name}")
        
        # Backup file
        backup_path = self.backup_dir / file_path.name
        shutil.copy2(file_path, backup_path)
        
        # Extract context
        context = self.extract_context(file_path, sorry_info['line'])
        
        best_error = None
        original_content = file_path.read_text()
        
        for iteration in range(self.max_iterations):
            print(f"\n  Iteration {iteration + 1}/{self.max_iterations}")
            
            # Generate proof
            proof = self.generate_proof(sorry_info, context, iteration, best_error)
            
            if not proof:
                print("  Failed to generate proof")
                continue
                
            print(f"  Generated: {proof[:100]}..." if len(proof) > 100 else f"  Generated: {proof}")
            
            # Apply proof
            self.apply_proof(file_path, sorry_info['line'], proof)
            
            # Check compilation
            success, error = self.check_compilation(file_path)
            
            if success:
                print("  ✓ SUCCESS! Proof compiles.")
                self.stats['compile_successes'] += 1
                self.stats['resolved_sorries'] += 1
                return True
            else:
                print(f"  ✗ Compilation failed")
                self.stats['compile_failures'] += 1
                
                # Extract error for next iteration
                if error:
                    best_error = self.extract_first_error(error)
                    print(f"  Error: {best_error}")
                    
                # Restore original
                file_path.write_text(original_content)
                
        print("  All iterations failed. Sorry remains.")
        return False
        
    def solve_file(self, file_path: Path, max_sorries=1):
        """Solve sorries in a file, limiting to max_sorries at a time"""
        
        if not file_path.exists():
            print(f"File not found: {file_path}")
            return
            
        print(f"\nProcessing: {file_path}")
        
        # Find all sorries
        sorries = self.find_sorries(file_path)
        self.stats['total_sorries'] += len(sorries)
        
        if not sorries:
            print("  No sorries found")
            return
            
        print(f"  Found {len(sorries)} sorries")
        
        # Process only up to max_sorries
        sorries_to_process = sorries[:max_sorries]
        print(f"  Processing {len(sorries_to_process)} sorry(ies) this run")
        
        # Process each sorry
        for sorry_info in sorries_to_process:
            self.solve_sorry(file_path, sorry_info)
            
    def report_statistics(self):
        """Print final statistics"""
        
        print(f"\n{'='*60}")
        print("FINAL STATISTICS")
        print('='*60)
        print(f"Total sorries found: {self.stats['total_sorries']}")
        print(f"Sorries resolved: {self.stats['resolved_sorries']}")
        
        if self.stats['total_sorries'] > 0:
            success_rate = self.stats['resolved_sorries'] / self.stats['total_sorries']
            print(f"Success rate: {success_rate:.1%}")
            
        print(f"LLM calls: {self.stats['llm_calls']}")
        print(f"Compilation successes: {self.stats['compile_successes']}")
        print(f"Compilation failures: {self.stats['compile_failures']}")
        print(f"\nBackups saved to: {self.backup_dir}")

def main():
    import sys
    
    # Get API key from command line
    if len(sys.argv) > 1:
        api_key = sys.argv[1]
    else:
        print("Please provide OpenAI API key as argument")
        return
        
    solver = RiemannHypothesisO3Solver(api_key)
    
    # Start with just one file and one sorry
    test_file = Path("test_sorry.lean")
    
    if not test_file.exists():
        print(f"Test file not found: {test_file}")
        print("Looking for other candidates...")
        
        # Find a file with few sorries
        framework_dir = Path("rh/academic_framework")
        candidates = []
        
        for lean_file in framework_dir.rglob("*.lean"):
            sorries = solver.find_sorries(lean_file)
            if 1 <= len(sorries) <= 3:
                candidates.append((lean_file, len(sorries)))
                
        if candidates:
            candidates.sort(key=lambda x: x[1])
            test_file = candidates[0][0]
            print(f"Selected: {test_file} with {candidates[0][1]} sorries")
        else:
            print("No suitable test files found")
            return
    
    print("=== RIEMANN HYPOTHESIS O3 SOLVER ===")
    print(f"Model: {solver.model}")
    print(f"Starting with ONE sorry in: {test_file}")
    print("-" * 60)
    
    # Start with just 1 sorry
    solver.solve_file(test_file, max_sorries=1)
    solver.report_statistics()
    
    # If successful, offer to continue
    if solver.stats['resolved_sorries'] > 0:
        print("\n✓ Successfully resolved a sorry!")
        print("You can now gradually increase max_sorries in the solve_file call")

if __name__ == "__main__":
    main() 