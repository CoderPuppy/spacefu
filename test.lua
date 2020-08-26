local ffi = require 'ffi'

local glfw; do
	glfw = {}
	glfw.lib = ffi.load 'glfw'
	ffi.cdef [[
		int glfwInit(void);
		void glfwTerminate(void);
		void glfwWindowHint(int, int);
		enum {
			GLFW_CONTEXT_VERSION_MAJOR = 0x00022002,
			GLFW_CONTEXT_VERSION_MINOR = 0x00022003,
			GLFW_OPENGL_PROFILE        = 0x00022008,
			GLFW_OPENGL_FORWARD_COMPAT = 0x00022006,
			GLFW_RESIZABLE             = 0x00020003
		};
		enum {
			GLFW_OPENGL_CORE_PROFILE   = 0x00032001
		};
		typedef struct GLFWwindow GLFWwindow;
		typedef struct GLFWmonitor GLFWmonitor;
		GLFWwindow* glfwCreateWindow(int width, int height, const char *title, GLFWmonitor *monitor, GLFWwindow *share);
		void glfwMakeContextCurrent(GLFWwindow *window);
		int glfwWindowShouldClose(GLFWwindow *window);
		int glfwWindowShouldClose(GLFWwindow *window);
		void glfwSwapBuffers(GLFWwindow *window);
		void glfwPollEvents(void);
	]]
	glfw.init = glfw.lib.glfwInit
	glfw.terminate = glfw.lib.glfwTerminate
	glfw.hints = setmetatable({}, {
		__index = function(self, k)
			error('getting hints is not supported')
		end;
		__newindex = function(self, k, v)
			if k == 'version_major' then
				glfw.lib.glfwWindowHint(glfw.lib.GLFW_CONTEXT_VERSION_MAJOR, v)
			elseif k == 'version_minor' then
				glfw.lib.glfwWindowHint(glfw.lib.GLFW_CONTEXT_VERSION_MINOR, v)
			elseif k == 'profile' then
				if v == 'core' then
					v = glfw.lib.GLFW_OPENGL_CORE_PROFILE
				else
					error(('unsupported profile: %q'):format(tostring(v)))
				end
				glfw.lib.glfwWindowHint(glfw.lib.GLFW_OPENGL_PROFILE, v)
			elseif k == 'forward_compat' then
				assert(type(v) == 'boolean')
				glfw.lib.glfwWindowHint(glfw.lib.GLFW_OPENGL_FORWARD_COMPAT, v)
			elseif k == 'resizable' then
				assert(type(v) == 'boolean')
				glfw.lib.glfwWindowHint(glfw.lib.GLFW_RESIZABLE, v)
			else
				error(('unsupported hint: %q'):format(tostring(k)))
			end
		end;
	})
	glfw.create_window = function(opts)
		return assert(glfw.lib.glfwCreateWindow(
			assert(opts.width, 'width required'),
			assert(opts.height, 'height required'),
			assert(opts.title, 'title required'),
			opts.monitor,
			opts.share
		), 'error')
	end
	glfw.make_context_current = glfw.lib.glfwMakeContextCurrent
	glfw.window_should_close = function(window)
		return glfw.lib.glfwWindowShouldClose(window) ~= 0
	end
	glfw.swap_buffers = glfw.lib.glfwSwapBuffers
	glfw.poll_events = glfw.lib.glfwPollEvents
end

local gl; do
	gl = {}
	gl.lib = ffi.load 'GLEW'
	ffi.cdef [[
		unsigned char glewExperimental;
		unsigned int glewInit(void);

		void glDrawElementsInstanced(unsigned int mode, int count, unsigned int type, const void *indices, int primcount);
		void glVertexAttribDivisor(unsigned int index, unsigned int divisor);
		void glVertexAttribPointer(unsigned int index, int size, unsigned int type, unsigned char normalized, int stride, const void *offset);
		void glVertexAttribIPointer(unsigned int index, int size, unsigned int type, int stride, const void *offset);
		void glVertexAttribLPointer(unsigned int index, int size, unsigned int type, int stride, const void *offset);
		int glGetAttribLocation(unsigned int program, const char *name);
		void glEnableVertexAttribArray(unsigned int index);
		void glGenBuffers(int n, unsigned int *buffers);
		void glBindBuffer(unsigned int target, unsigned int buffer);
		void glBufferData(unsigned int target, ptrdiff_t size, const void *data, unsigned int usage);
		unsigned int glCreateShader(unsigned int type);
		void glShaderSource(unsigned int shader, int count, const char **string, const int *length);
		void glGetShaderiv(unsigned int shader, unsigned int pname, int *params);
		void glCompileShader(unsigned int shader);
		unsigned int glCreateProgram(void);
		void glAttachShader(unsigned int program, unsigned int shader);
		void glLinkProgram(unsigned int program);

		enum {
			GL_ARRAY_BUFFER = 0x8892,
			GL_STATIC_DRAW = 0x88E4,
			GL_VERTEX_SHADER = 0x8B31,
			GL_FRAGMENT_SHADER = 0x8B30,
			GL_COMPILE_STATUS = 0x8B81
		};
	]]
	gl.lib.glewExperimental = true -- TODO: minor hack
	gl.glew_init = gl.lib.glewInit
	gl.draw_elements_instanced = gl.lib.glDrawElementsInstanced
	gl.vertex_attrib_divisor = gl.lib.glVertexAttribDivisor
	-- TODO: types
	gl.vertex_attrib_float_pointer = gl.lib.glVertexAttribPointer
	gl.vertex_attrib_int_pointer = gl.lib.glVertexAttribIPointer
	gl.vertex_attrib_double_pointer = gl.lib.glVertexAttribLPointer
	gl.get_attrib_location = gl.lib.glGetAttribLocation
	gl.gen_buffers = function(n)
		n = n or 1
		local arr = ffi.new('unsigned int[?]', n)
		gl.lib.glGenBuffers(n, arr)
		if n == 1 then
			return arr[0]
		else
			local t = {}
			for i = 1, n do
				t[i] = arr[i - 1]
			end
			return table.unpack(t, 1, n)
		end
	end
	local function handle_target(target)
		if target == 'array_buffer' then
			target = gl.lib.GL_ARRAY_BUFFER
		else
			error(('unhandled target: %q'):format(tostring(target)))
		end
		return target
	end
	gl.bind_buffer = function(target, buffer)
		target = handle_target(target)
		gl.lib.glBindBuffer(target, buffer)
	end
	gl.buffer_data = function(target, data, size, frequency, purpose)
		target = handle_target(target)
		local usage
		if frequency == 'static' and purpose == 'draw' then
			usage = gl.lib.GL_STATIC_DRAW
		else
			error(('unhandled frequency, purpose pair: %q, %q'):Format(tostring(frequency), tostring(purpose)))
		end
		gl.lib.glBufferData(target, size, data, usage)
	end
	gl.create_shader = function(typ)
		if typ == 'vertex' then
			typ = gl.lib.GL_VERTEX_SHADER
		elseif typ == 'fragment' then
			typ = gl.lib.GL_FRAGMENT_SHADER
		else
			error(('unhandled shader type: %q'):format(tostring(typ)))
		end
		return gl.lib.glCreateShader(typ)
	end
	gl.shader_source = function(shader, ...)
		local n = select('#', ...)
		local strs = ffi.new('const char*[?]', n)
		local lens = ffi.new('int[?]', n)
		for i = 1, n do
			local str = select(i, ...)
			strs[i - 1] = str
			lens[i - 1] = #str
		end
		gl.lib.glShaderSource(shader, n, strs, lens)
	end
	gl.get_shader = function(shader, pname)
		if pname == 'compile_status' then
			pname = gl.lib.GL_COMPILE_STATUS
		else
			error(('unhandled parameter name: %q'):format(tostring(pname)))
		end
		local buf = ffi.new('int[1]')
		gl.lib.glGetShaderiv(shader, pname, buf)
		return buf[0]
	end
	gl.compile_shader = gl.lib.glCompileShader
	gl.make_shader = function(typ, ...)
		local shader = gl.create_shader(typ)
		gl.shader_source(shader, ...)
		gl.compile_shader(shader)
		if gl.get_shader(shader, 'compile_status') == 0 then
			error('compile failed')
		end
		return shader
	end
	gl.create_program = gl.lib.glCreateProgram
	gl.attach_shader = gl.lib.glAttachShader
	gl.link_program = gl.lib.glLinkProgram
	gl.make_program = function(...)
		local program = gl.create_program()
		for i = 1, select('#', ...) do
			gl.attach_shader(program, (select(i, ...)))
		end
		gl.link_program(program)
		return program
	end
end

glfw.init()
glfw.hints.version_major = 3
glfw.hints.version_minor = 2
glfw.hints.profile = 'core'
glfw.hints.forward_compat = true
glfw.hints.resizable = true
local window = glfw.create_window {
	width = 800; height = 600;
	title = 'Spacefu';
}
glfw.make_context_current(window)
gl.glew_init()

local cube_verts = gl.gen_buffers()
gl.bind_buffer('array_buffer', cube_verts)
do
	local buf = ffi.new('float[?]', 8 * 3)
	for i, vert in ipairs {
		{0, 0, 0};
		{0, 0, 1};
		{0, 1, 0};
		{0, 1, 1};
		{1, 0, 0};
		{1, 0, 1};
		{1, 1, 0};
		{1, 1, 1};
	} do
		buf[(i - 1) * 3] = vert[1]
		buf[(i - 1) * 3 + 1] = vert[2]
		buf[(i - 1) * 3 + 2] = vert[3]
	end
	gl.buffer_data('array_buffer', buf, ffi.sizeof(buf), 'static', 'draw')
end

local vert_shader = gl.make_shader('vertex', [[
	#version 150 core

	void main() {
		gl_Position = vec4(0.0, 0.0, 0.0, 1.0);
	}
]])

local frag_shader = gl.make_shader('fragment', [[
	#version 150 core

	out vec4 outColor;

	void main() {
			outColor = vec4(1.0, 0.0, 0.0, 1.0);
	}
]])

local program = gl.make_program(vert_shader, frag_shader)

-- while not glfw.window_should_close(window) do
-- 	glfw.swap_buffers(window)
-- 	glfw.poll_events()
-- end
glfw.terminate()

-- instanced with instanced arrays
-- glDrawElementsInstanced
