package edu.boisestate.datagen.exprcompiler;

import edu.boisestate.datagen.utils.ClassPathUtils;
import freemarker.cache.StringTemplateLoader;
import freemarker.template.Configuration;
import freemarker.template.Template;
import freemarker.template.TemplateException;
import java.io.FileWriter;
import java.io.IOException;
import java.io.Writer;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.apache.commons.lang3.StringUtils;
import org.tinylog.Logger;

public class CompiledExpression {

    public Set<String> variables;
    public String sExpr;

    public String toString() {
        return sExpr;
    }

    public boolean equals(Object obj) {
        if (obj == null) return false;
        if (obj == this) return true;
        if (!(obj instanceof CompiledExpression)) return false;

        CompiledExpression other = (CompiledExpression) obj;

        // Check if variables differ. If they do, we can return false.
        boolean varsCheck = variables.equals(other.variables);
        if (!varsCheck) {
            return false;
        }

        boolean earlyCheck =
            sExpr.equals(other.sExpr) && variables.equals(other.variables);

        if (earlyCheck) {
            // No need to run SMT. They are identical with a simple text diff.
            return true;
        } else {
            Logger.info("Running SMT check");
            // Need to run z3 here.

            String z3BinaryPath = ClassPathUtils.getBinaryPath("z3");

            if (z3BinaryPath == null) {
                System.err.println("Could not find z3 binary in PATH.");
                return false;
            }

            // Generate a "jumbo" hashset of all variables, so that both functions
            // can share them.

            HashSet<String> allVariables = new HashSet<String>();
            allVariables.addAll(variables);
            allVariables.addAll(other.variables);
            List<String> variableList = new ArrayList<>(allVariables);

            // Generate a SMT file to query with z3.
            String smtFile = "tmp.smt2";

            Map<String, Object> data = new HashMap<String, Object>();
            data.put("variables", variableList);
            data.put("conjunction_first", sExpr);
            data.put("conjunction_second", other.sExpr);

            Configuration cfg = new Configuration(Configuration.VERSION_2_3_30);
            cfg.setDefaultEncoding("UTF-8");

            StringTemplateLoader loader = new StringTemplateLoader();
            loader.putTemplate(
                "smt.ftl",
                SMTTemplate.getTemplate(
                    variableList.toArray(new String[0]),
                    sExpr,
                    other.sExpr
                )
            );
            cfg.setTemplateLoader(loader);

            try (Writer writer = new FileWriter(smtFile)) {
                Template template = cfg.getTemplate("smt.ftl");
                template.process(data, writer);
            } catch (IOException | TemplateException e) {
                throw new RuntimeException("Error processing template", e);
            }

            // Run z3 on the generated SMT file.
            String[] cmd = { z3BinaryPath, smtFile };
            ProcessBuilder pb = new ProcessBuilder(cmd);
            Process p = null;

            try {
                p = pb.start();
                p.waitFor();
            } catch (IOException e) {
                e.printStackTrace();
                System.exit(1);
            } catch (InterruptedException e) {
                e.printStackTrace();
                System.exit(1);
            }

            // Split the output of z3.
            // line by line, get each line, and check if "sat" is in the line
            // For empty expressions, we will get 4 lines, but "sat" "sat" lines also,
            // so we care only about that condition.

            java.io.InputStream is = p.getInputStream();
            java.io.BufferedReader reader = new java.io.BufferedReader(
                new java.io.InputStreamReader(is)
            );

            String line = "";
            ArrayList<String> satlines = new ArrayList<String>();
            try {
                while ((line = reader.readLine()) != null) {
                    if (line.contains("sat")) {
                        satlines.add(StringUtils.chomp(line.strip()));
                        return true;
                    }
                }
            } catch (IOException e) {
                e.printStackTrace();
                System.err.println("There was an error reading z3 output");
                System.exit(1);
            }

            // before returning, delete the smt file.
            // File smt = new File(smtFile);
            // smt.delete();

            return Arrays.asList("sat", "sat").equals(satlines);
        }
    }
}
