.PHONY: update-exos

update-exos:
	@head -n -3 README.md > README.md.tmp; \
	mv README.md.tmp README.md; \
	skipped=$$(grep -Fho -- '#skipexo()' ./*.typ | wc -l); \
	solved=$$(grep -Fho -- '#exo()' ./*.typ | wc -l); \
	total=217; \
	{ \
	  printf -- '- Solved exercises: %s\n' "$$solved"; \
	  printf -- '- Skipped exercises: %s\n' "$$skipped"; \
	  printf -- '- Total exercises: %s\n' "$$total"; \
	} | tee -a README.md
