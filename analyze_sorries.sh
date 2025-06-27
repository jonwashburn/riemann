#!/bin/bash

# Academic Framework Sorry Analysis Script
# Generates a detailed report of all sorries in the academic framework

echo "Academic Framework Sorry Analysis"
echo "================================="
echo ""

# Change to academic framework directory
cd rh/academic_framework

# Count total sorries
total_sorries=$(grep -r "sorry" . --include="*.lean" | wc -l)
echo "Total sorries found: $total_sorries"
echo ""

# Generate summary by file
echo "Sorry count by file:"
echo "-------------------"
for file in $(find . -name "*.lean" -exec grep -l "sorry" {} \; | sort); do
    count=$(grep -c "sorry" "$file")
    printf "%-50s %3d\n" "$file" "$count"
done | sort -k2 -nr
echo ""

# Generate detailed report
echo "Generating detailed sorry report..."
echo ""

# Create detailed report file
cat > sorry_detailed_report.md << 'EOF'
# Academic Framework Sorry Analysis Report

Generated on: $(date)

## Summary Statistics
- Total sorries: $total_sorries
- Files with sorries: $(find . -name "*.lean" -exec grep -l "sorry" {} \; | wc -l)

## Detailed Analysis by File

EOF

# Add details for each file
for file in $(find . -name "*.lean" -exec grep -l "sorry" {} \; | sort); do
    echo "### $file" >> sorry_detailed_report.md
    echo "" >> sorry_detailed_report.md
    echo "Sorry count: $(grep -c "sorry" "$file")" >> sorry_detailed_report.md
    echo "" >> sorry_detailed_report.md
    echo '```lean' >> sorry_detailed_report.md
    
    # Extract context around each sorry
    grep -n -B2 -A2 "sorry" "$file" | sed 's/^/Line /' >> sorry_detailed_report.md
    
    echo '```' >> sorry_detailed_report.md
    echo "" >> sorry_detailed_report.md
done

echo "Detailed report saved to: rh/academic_framework/sorry_detailed_report.md"
echo ""

# Categorize common patterns
echo "Common sorry patterns:"
echo "---------------------"
echo ""

echo "1. Summability proofs:"
grep -h -B2 "sorry" . --include="*.lean" -r | grep -i "summable" | wc -l

echo "2. Continuity proofs:"
grep -h -B2 "sorry" . --include="*.lean" -r | grep -i "continuous" | wc -l

echo "3. Convergence proofs:"
grep -h -B2 "sorry" . --include="*.lean" -r | grep -i "converge\|tendsto" | wc -l

echo "4. Norm/bound proofs:"
grep -h -B2 "sorry" . --include="*.lean" -r | grep -i "norm\|bound" | wc -l

echo "5. Determinant proofs:"
grep -h -B2 "sorry" . --include="*.lean" -r | grep -i "det\|determinant" | wc -l

echo ""
echo "Quick win opportunities (likely in mathlib):"
echo "-------------------------------------------"

# Look for sorries with simple goals
grep -h -B1 "sorry" . --include="*.lean" -r | grep -E "Summable|Continuous|tendsto_" | head -10

echo ""
echo "Analysis complete!"
echo ""
echo "Next steps:"
echo "1. Review sorry_detailed_report.md"
echo "2. Start with files that have fewer sorries"
echo "3. Look for patterns that can be solved with the same technique" 